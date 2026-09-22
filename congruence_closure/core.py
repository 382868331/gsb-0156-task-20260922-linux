"""Congruence closure over ground terms with proof production and rollback.

Terms are constants or fixed-arity function applications, stored in a shared
(hash-consed) DAG.  Equality is closed under congruence: if two applications
use the same symbol and their arguments are pairwise equal, the applications
are equal.  The converse is *not* derivable (f(a) = f(b) does not imply a = b).

Implementation: union-find (union by size, no path compression so that every
mutation is undoable) plus a signature table keyed by
``(symbol, tuple(find(arg) for arg in args))``.  After each merge only the
parents of the moved (smaller) class are re-registered, so the algorithm never
compares all pairs of terms.  Every union records its reason in a proof
forest; ``explain`` walks the unique path in that forest and emits a proof
tree that can be checked independently by :func:`congruence_closure.verify_proof`.

All public mutating operations are transactional: on any error (conflict,
budget exhaustion, invalid input) the engine state is rolled back to exactly
what it was before the call, via an undo log.
"""

from __future__ import annotations

import math
import sys
from collections import deque
from contextlib import contextmanager

DEFAULT_MAX_TERMS = 5000
DEFAULT_WORK_BUDGET = 1_000_000


# ---------------------------------------------------------------------------
# Errors
# ---------------------------------------------------------------------------

class CongruenceClosureError(Exception):
    """Base class for all errors raised by this module."""


class InvalidInputError(CongruenceClosureError, ValueError):
    """An argument violates the public contract.

    The ``param`` attribute names the offending parameter when known.
    """

    def __init__(self, message, *, param=None):
        super().__init__(message)
        self.param = param


class LimitExceededError(CongruenceClosureError):
    """The shared-DAG node budget (``max_terms``) is exhausted."""


class BudgetExhaustedError(CongruenceClosureError):
    """The per-call propagation work budget is exhausted.

    This is distinct from "no proof exists" (:class:`NotEqualError`) and from
    a logical conflict (:class:`ConflictError`): it means the engine was not
    allowed enough steps to finish propagating, and the call was rolled back.
    """


class NotEqualError(CongruenceClosureError):
    """``explain`` was requested for terms that are not equal (no proof exists)."""


class ConflictError(CongruenceClosureError):
    """A distinctness constraint is violated by the asserted equalities.

    Attributes:
        pair: ``(a, b)`` term ids of the violated constraint.
        proof: proof tree of ``a == b`` (checkable by ``verify_proof``).
        input_equalities: structural input equalities that the proof's
            ``("input", k)`` leaves refer to, captured at raise time so the
            proof stays verifiable even after the failed call is rolled back.
    """

    def __init__(self, a, b, proof, input_equalities):
        super().__init__(
            f"distinctness constraint violated: terms {a} and {b} are provably equal"
        )
        self.pair = (a, b)
        self.proof = proof
        self.input_equalities = input_equalities


# ---------------------------------------------------------------------------
# Validation helpers
# ---------------------------------------------------------------------------

def _check_int(value, param):
    """Reject bools, NaN/Infinity and any non-int; return ``value``."""
    if isinstance(value, bool):
        raise InvalidInputError(
            f"{param} must be an integer, got bool {value!r}", param=param)
    if isinstance(value, float):
        if math.isnan(value) or math.isinf(value):
            raise InvalidInputError(
                f"{param} must be a finite integer, got {value!r}", param=param)
        raise InvalidInputError(
            f"{param} must be an integer, got float {value!r}", param=param)
    if not isinstance(value, int):
        raise InvalidInputError(
            f"{param} must be an integer, got {type(value).__name__} {value!r}",
            param=param)
    return value


@contextmanager
def _recursion_guard(min_limit):
    """Temporarily raise the recursion limit (term DAGs may be deep)."""
    old = sys.getrecursionlimit()
    if old >= min_limit:
        yield
        return
    sys.setrecursionlimit(min_limit)
    try:
        yield
    finally:
        sys.setrecursionlimit(old)


# ---------------------------------------------------------------------------
# Engine
# ---------------------------------------------------------------------------

class CongruenceClosure:
    """Congruence-closure engine over a shared DAG of ground terms.

    Parameters:
        max_terms: maximum number of DAG nodes (default 5000).
        work_budget: maximum propagation steps (union operations plus
            signature computations) allowed per public mutating call.
            Exhaustion raises :class:`BudgetExhaustedError` and rolls the
            call back; it is never reported as a logical conflict.
    """

    def __init__(self, *, max_terms=DEFAULT_MAX_TERMS, work_budget=DEFAULT_WORK_BUDGET):
        _check_int(max_terms, "max_terms")
        if max_terms < 1:
            raise InvalidInputError(
                f"max_terms must be >= 1, got {max_terms}", param="max_terms")
        _check_int(work_budget, "work_budget")
        if work_budget < 0:
            raise InvalidInputError(
                f"work_budget must be >= 0, got {work_budget}", param="work_budget")
        self._max_terms = max_terms
        self._budget_limit = work_budget
        self._budget = work_budget

        self._terms = []        # id -> (symbol, tuple of arg ids)
        self._hashcons = {}     # (symbol, args) -> id
        self._arities = {}      # symbol -> fixed arity
        self._parent = []       # union-find parent (no path compression)
        self._size = []         # class size, valid at roots
        self._members = []      # root -> list of member term ids
        self._uses = []         # term -> list of parent (direct user) term ids
        self._sig = {}          # signature -> term id (lazy, may be stale)
        self._proof_adj = []    # term -> [(neighbour, label)]; a forest
        self._inputs = []       # asserted equalities, as (id, id)
        self._distincts = []    # asserted distinctness pairs, as (id, id)
        self._forbidden = []    # root -> [(member, other)] distinctness entries
        self._num_classes = 0
        self._undo = []         # undo log for transactional rollback

    # -- introspection -----------------------------------------------------

    @property
    def term_count(self):
        """Number of DAG nodes created so far."""
        return len(self._terms)

    @property
    def class_count(self):
        """Current number of equivalence classes."""
        return self._num_classes

    def term(self, t):
        """Return ``(symbol, (arg_id, ...))`` for term id ``t``."""
        tid = self._check_term_id(t, "t")
        sym, args = self._terms[tid]
        return (sym, tuple(args))

    def term_structure(self, t):
        """Return the fully structural form ``(symbol, (subterm, ...))``."""
        tid = self._check_term_id(t, "t")
        with _recursion_guard(self._rec_limit()):
            return self._structure(tid)

    def input_equalities(self):
        """Structural form of every recorded input equality, in order.

        The k-th pair is what a ``("input", k)`` proof leaf refers to.
        """
        with _recursion_guard(self._rec_limit()):
            return [(self._structure(a), self._structure(b))
                    for a, b in self._inputs]

    def are_equal(self, a, b):
        """True iff terms ``a`` and ``b`` are equal in the current closure."""
        aid = self._check_term_id(a, "a")
        bid = self._check_term_id(b, "b")
        return self._find(aid) == self._find(bid)

    # -- validation ----------------------------------------------------------

    def _check_term_id(self, value, param):
        _check_int(value, param)
        if not 0 <= value < len(self._terms):
            raise InvalidInputError(
                f"{param}: unknown term id {value!r} "
                f"({len(self._terms)} terms exist)", param=param)
        return value

    def _check_pair(self, pair, param):
        if isinstance(pair, (list, tuple)) and len(pair) == 2:
            return pair[0], pair[1]
        raise InvalidInputError(
            f"{param} must be a (term_id, term_id) pair, got {pair!r}",
            param=param)

    def _rec_limit(self):
        return max(10_000, 8 * self._max_terms + 200)

    # -- union-find (no path compression; every change is logged) -----------

    def _find(self, x):
        while self._parent[x] != x:
            x = self._parent[x]
        return x

    # -- term construction ---------------------------------------------------

    def add_term(self, symbol, args=()):
        """Add ``symbol(args...)`` to the shared DAG and return its id.

        Hash-consed: an identical application returns the existing id.
        Constants are arity-0 applications (``add_term("c")``).  Each symbol
        has a fixed arity; reusing it with a different arity is an error.
        Adding a term whose signature already exists may trigger congruence
        merges; a resulting conflict rolls the whole call back.
        """
        self._budget = self._budget_limit
        mark = len(self._undo)
        try:
            return self._add_term(symbol, args)
        except Exception:
            self._rollback(mark)
            raise

    def _add_term(self, symbol, args):
        if not isinstance(symbol, str) or isinstance(symbol, bool):
            raise InvalidInputError(
                f"symbol must be a non-empty str, got "
                f"{type(symbol).__name__} {symbol!r}", param="symbol")
        if not symbol:
            raise InvalidInputError("symbol must be a non-empty str, got ''",
                                    param="symbol")
        if not isinstance(args, (list, tuple)):
            raise InvalidInputError(
                f"args must be a list or tuple of term ids, got "
                f"{type(args).__name__}", param="args")
        arg_ids = tuple(self._check_term_id(a, f"args[{i}]")
                        for i, a in enumerate(args))
        arity = len(arg_ids)
        known = self._arities.get(symbol)
        if known is not None and known != arity:
            raise InvalidInputError(
                f"arity mismatch for symbol {symbol!r}: previously used with "
                f"arity {known}, now {arity}", param="args")

        key = (symbol, arg_ids)
        existing = self._hashcons.get(key)
        if existing is not None:
            return existing
        if len(self._terms) >= self._max_terms:
            raise LimitExceededError(
                f"term limit reached: max_terms={self._max_terms}")

        tid = len(self._terms)
        self._terms.append(key)
        self._hashcons[key] = tid
        self._parent.append(tid)
        self._size.append(1)
        self._members.append([tid])
        self._uses.append([])
        self._proof_adj.append([])
        self._forbidden.append([])
        self._num_classes += 1
        self._undo.append(("term", tid))
        for a in arg_ids:
            self._uses[a].append(tid)
            self._undo.append(("uses", a))
        self._arities.setdefault(symbol, arity)

        todo = []
        self._register_sig(tid, todo)
        self._drain(todo)
        return tid

    # -- assertions ----------------------------------------------------------

    def assert_equal(self, a, b):
        """Assert ``a == b`` and close under congruence.

        Returns True if a merge happened, False if the terms were already
        equal.  On :class:`ConflictError` / :class:`BudgetExhaustedError` the
        engine is rolled back to the state before this call.
        """
        self._budget = self._budget_limit
        mark = len(self._undo)
        try:
            return self._assert_equal(a, b)
        except Exception:
            self._rollback(mark)
            raise

    def _assert_equal(self, a, b):
        aid = self._check_term_id(a, "a")
        bid = self._check_term_id(b, "b")
        if self._find(aid) == self._find(bid):
            return False
        k = len(self._inputs)
        self._inputs.append((aid, bid))
        self._undo.append(("input_reg",))
        self._drain([(aid, bid, ("input", k))])
        return True

    def assert_distinct(self, a, b):
        """Assert that ``a`` and ``b`` must stay different.

        Raises :class:`ConflictError` (carrying a verifiable proof) if they
        are already equal; otherwise records the constraint so that any later
        merge making them equal raises :class:`ConflictError` and rolls back.
        """
        self._budget = self._budget_limit
        mark = len(self._undo)
        try:
            self._assert_distinct(a, b)
        except Exception:
            self._rollback(mark)
            raise

    def _assert_distinct(self, a, b):
        aid = self._check_term_id(a, "a")
        bid = self._check_term_id(b, "b")
        if self._find(aid) == self._find(bid):
            self._raise_conflict(aid, bid)
        self._distincts.append((aid, bid))
        self._undo.append(("distinct",))
        ra, rb = self._find(aid), self._find(bid)
        self._forbidden[ra].append((aid, bid))
        self._undo.append(("forbid", ra, 1))
        self._forbidden[rb].append((bid, aid))
        self._undo.append(("forbid", rb, 1))

    def assert_batch(self, equalities=(), distincts=()):
        """Apply a batch of assertions atomically.

        ``equalities`` and ``distincts`` are sequences of ``(a, b)`` term-id
        pairs.  Equalities are applied first, then distinctness constraints.
        If any element is invalid or a conflict occurs, every change made by
        this call is rolled back and the exception propagates.
        """
        if not isinstance(equalities, (list, tuple)):
            raise InvalidInputError(
                f"equalities must be a list or tuple of pairs, got "
                f"{type(equalities).__name__}", param="equalities")
        if not isinstance(distincts, (list, tuple)):
            raise InvalidInputError(
                f"distincts must be a list or tuple of pairs, got "
                f"{type(distincts).__name__}", param="distincts")
        self._budget = self._budget_limit
        mark = len(self._undo)
        try:
            for i, pair in enumerate(equalities):
                a, b = self._check_pair(pair, f"equalities[{i}]")
                self._assert_equal(a, b)
            for i, pair in enumerate(distincts):
                a, b = self._check_pair(pair, f"distincts[{i}]")
                self._assert_distinct(a, b)
        except Exception:
            self._rollback(mark)
            raise

    # -- explanation ---------------------------------------------------------

    def explain(self, a, b):
        """Return a proof tree for ``a == b``.

        Raises :class:`NotEqualError` if the terms are not equal (no proof
        exists).  The returned tree uses the nodes ``("input", k)``,
        ``("cong", symbol, subproofs)``, ``("trans", p, q)``,
        ``("symm", p)`` and ``("refl", structural_term)``; it can be checked
        independently with :func:`congruence_closure.verify_proof` together
        with :meth:`input_equalities`.  Repeated calls with the same engine
        state return identical trees.
        """
        aid = self._check_term_id(a, "a")
        bid = self._check_term_id(b, "b")
        if self._find(aid) != self._find(bid):
            raise NotEqualError(
                f"terms {aid} and {bid} are not equal; no proof exists")
        with _recursion_guard(self._rec_limit()):
            return self._explain(aid, bid)

    def _explain(self, x, y):
        if x == y:
            return ("refl", self._structure(x))
        steps = [self._edge_proof(u, v, label)
                 for (u, v, label) in self._forest_path(x, y)]
        proof = steps[0]
        for step in steps[1:]:
            proof = ("trans", proof, step)
        return proof

    def _forest_path(self, x, y):
        """Unique path from x to y in the proof forest, as (u, v, label)."""
        prev = {x: None}
        queue = deque([x])
        while queue:
            u = queue.popleft()
            if u == y:
                break
            for v, label in self._proof_adj[u]:
                if v not in prev:
                    prev[v] = (u, label)
                    queue.append(v)
        edges = []
        cur = y
        while cur != x:
            u, label = prev[cur]
            edges.append((u, cur, label))
            cur = u
        edges.reverse()
        return edges

    def _edge_proof(self, u, v, label):
        """Proof of u == v from a single forest edge traversed u -> v."""
        if label[0] == "input":
            k = label[1]
            l, r = self._inputs[k]
            proof = ("input", k)
            return proof if (u, v) == (l, r) else ("symm", proof)
        # congruence edge: label = ("cong", t1, t2), endpoints are t1, t2
        _, t1, t2 = label
        sym, args1 = self._terms[t1]
        _, args2 = self._terms[t2]
        subs = tuple(self._explain(x, y) for x, y in zip(args1, args2))
        proof = ("cong", sym, subs)
        return proof if (u, v) == (t1, t2) else ("symm", proof)

    def _structure(self, t):
        sym, args = self._terms[t]
        return (sym, tuple(self._structure(a) for a in args))

    # -- core propagation ----------------------------------------------------

    def _spend(self):
        self._budget -= 1
        if self._budget < 0:
            raise BudgetExhaustedError(
                f"work budget exhausted (work_budget={self._budget_limit}); "
                f"the call was rolled back")

    def _signature_of(self, t):
        sym, args = self._terms[t]
        return (sym, tuple(self._find(a) for a in args))

    def _congruent(self, t, q):
        sa, aa = self._terms[t]
        sb, ab = self._terms[q]
        return sa == sb and all(self._find(x) == self._find(y)
                                for x, y in zip(aa, ab))

    def _set_sig(self, key, value):
        if key in self._sig:
            self._undo.append(("sig", key, True, self._sig[key]))
        else:
            self._undo.append(("sig", key, False, None))
        self._sig[key] = value

    def _register_sig(self, t, todo):
        """(Re-)register ``t`` under its current signature; schedule merges."""
        self._spend()
        s = self._signature_of(t)
        if s in self._sig:
            q = self._sig[s]
            if self._congruent(t, q):
                if self._find(t) != self._find(q):
                    todo.append((t, q, ("cong", t, q)))
                self._set_sig(s, t)
            else:
                # Stale entry: q's signature changed since it was stored.
                self._set_sig(s, t)
        else:
            self._set_sig(s, t)

    def _drain(self, todo):
        while todo:
            u, v, reason = todo.pop()
            ru, rv = self._find(u), self._find(v)
            if ru == rv:
                continue
            self._spend()
            if self._size[ru] > self._size[rv]:
                ru, rv = rv, ru
            # Proof edge between the two terms named by the reason.
            self._proof_adj[u].append((v, reason))
            self._proof_adj[v].append((u, reason))
            self._undo.append(("edge", u, v))
            # Union by size: attach the smaller class ru under rv.
            self._parent[ru] = rv
            self._size[rv] += self._size[ru]
            self._undo.append(("union", ru, rv))
            self._num_classes -= 1
            self._undo.append(("classes",))
            moved = self._members[ru]
            self._members[rv].extend(moved)
            self._undo.append(("members", rv, len(moved)))
            # Distinctness: any constraint (x, y) with x in the moved class
            # and y now in the merged class is violated.
            for (x, y) in self._forbidden[ru]:
                if self._find(y) == rv:
                    self._raise_conflict(x, y)
            if self._forbidden[ru]:
                self._forbidden[rv].extend(self._forbidden[ru])
                self._undo.append(("forbid", rv, len(self._forbidden[ru])))
            # Congruence: only parents of moved members can change signature.
            for m in moved:
                for p in self._uses[m]:
                    self._register_sig(p, todo)

    def _raise_conflict(self, x, y):
        with _recursion_guard(self._rec_limit()):
            proof = self._explain(x, y)
            inputs = [(self._structure(a), self._structure(b))
                      for a, b in self._inputs]
        raise ConflictError(x, y, proof, inputs)

    # -- rollback --------------------------------------------------------------

    def _rollback(self, mark):
        while len(self._undo) > mark:
            entry = self._undo.pop()
            tag = entry[0]
            if tag == "union":
                _, child, parent = entry
                self._parent[child] = child
                self._size[parent] -= self._size[child]
            elif tag == "members":
                _, root, count = entry
                del self._members[root][len(self._members[root]) - count:]
            elif tag == "forbid":
                _, root, count = entry
                del self._forbidden[root][len(self._forbidden[root]) - count:]
            elif tag == "sig":
                _, key, present, old = entry
                if present:
                    self._sig[key] = old
                else:
                    del self._sig[key]
            elif tag == "edge":
                _, u, v = entry
                self._proof_adj[u].pop()
                self._proof_adj[v].pop()
            elif tag == "distinct":
                self._distincts.pop()
            elif tag == "input_reg":
                self._inputs.pop()
            elif tag == "classes":
                self._num_classes += 1
            elif tag == "uses":
                _, arg = entry
                self._uses[arg].pop()
            elif tag == "term":
                _, tid = entry
                sym, args = self._terms.pop()
                del self._hashcons[(sym, args)]
                self._parent.pop()
                self._size.pop()
                self._members.pop()
                self._uses.pop()
                self._proof_adj.pop()
                self._forbidden.pop()
                self._num_classes -= 1
            else:  # pragma: no cover - defensive
                raise AssertionError(f"unknown undo entry {entry!r}")
