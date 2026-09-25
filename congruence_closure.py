"""Congruence closure over a shared DAG of first-order terms.

A reusable, offline, proof-producing decision procedure for the theory of
equality with uninterpreted function symbols:

* terms are constants or fixed-arity function applications, hash-consed into
  a shared DAG (at most ``max_nodes`` nodes, 5000 by default);
* congruence is one-directional: equal arguments imply equal results for the
  same function symbol, but ``f(a) = f(b)`` never implies ``a = b``;
* union-find with a signature table over parent terms (no all-pairs
  comparison);
* every derived equality keeps its origin (an input equality or a congruence
  step), so ``explain`` returns an independently verifiable proof and a
  conflicting assertion returns a verifiable contradiction proof;
* every mutating operation is atomic: on conflict the operation (or the whole
  batch, for :meth:`CongruenceClosure.apply_batch`) is rolled back;
* scoped assumptions: :meth:`CongruenceClosure.push` /
  :meth:`CongruenceClosure.pop` bracket a layer of equalities, distinct
  assertions and new terms; popping undoes the whole layer (equivalence
  classes, parent signatures, proof forest and conflict state return to
  exactly what they were at ``push``) via a per-scope change journal --
  ``push`` itself never copies the term graph.

Standard library only.  Python 3.14.7.
"""

from __future__ import annotations

import contextlib
import sys

__all__ = [
    "DEFAULT_MAX_NODES",
    "CongruenceClosure",
    "CongruenceError",
    "ValidationError",
    "ArityError",
    "UnknownNodeError",
    "StaleNodeError",
    "NodeLimitError",
    "NotEqualError",
    "ContradictionError",
    "ScopeError",
    "ProofError",
    "verify_proof",
    "verify_contradiction",
    "term_to_str",
    "proof_to_str",
]

DEFAULT_MAX_NODES = 5000

_INPUT = "input"
_CONG = "cong"
_CONTRADICTION = "contradiction"

_ABSENT = object()  # journal sentinel: key did not exist at scope entry


# ---------------------------------------------------------------------------
# Errors
# ---------------------------------------------------------------------------

class CongruenceError(Exception):
    """Base class for all errors raised by this module."""


class ValidationError(CongruenceError, ValueError):
    """An argument failed validation; the message locates the parameter."""


class ArityError(ValidationError):
    """A function symbol was used with an arity different from its first use."""


class UnknownNodeError(ValidationError):
    """A node id is outside the range of existing nodes."""


class StaleNodeError(UnknownNodeError):
    """A node id created inside a scope that has since been popped.

    Node ids are never reused: a structurally identical term built after
    the pop gets a fresh id, so an old handle can never silently alias it.
    """


class NodeLimitError(CongruenceError):
    """The shared DAG already holds ``max_nodes`` nodes."""


class NotEqualError(CongruenceError):
    """``explain`` was asked to prove an equality that does not hold.

    The closure algorithm is complete and terminating, so this is a
    definitive "no proof exists", not an exhausted search budget.  The only
    resource bound in this module is the node limit (:class:`NodeLimitError`).
    """


class ProofError(CongruenceError):
    """A proof failed independent verification; the message locates the step."""


class ScopeError(CongruenceError):
    """``pop`` was called at the base level: there is no scope to leave."""


class ContradictionError(CongruenceError):
    """An assertion contradicts a previously asserted distinctness.

    Attributes form a self-contained proof bundle (valid even though the
    failed operation was rolled back):

    * ``proof``     -- ``("contradiction", equality_proof, (x, y))``
    * ``inputs``    -- frozenset of normalized input equalities the proof uses
    * ``distincts`` -- frozenset of normalized distinct assertions
    * ``terms``     -- tuple of ``(func, args)`` indexed by node id
    """

    def __init__(self, message, proof, inputs, distincts, terms):
        super().__init__(message)
        self.proof = proof
        self.inputs = inputs
        self.distincts = distincts
        self.terms = terms


class _Conflict(Exception):
    """Internal: a pending merge edge collided with a forbidden pair.

    ``pair`` is the original distinct pair ``(x, y)``; ``edge`` is the
    pending merge ``(a, b, reason)`` that would equate the two classes.
    """

    def __init__(self, pair, edge):
        super().__init__(pair)
        self.pair = pair
        self.edge = edge


def _norm_pair(a, b):
    return (a, b) if a <= b else (b, a)


def _ensure_recursion_limit(needed):
    current = sys.getrecursionlimit()
    if current < needed:
        sys.setrecursionlimit(needed)


# ---------------------------------------------------------------------------
# Core data structure
# ---------------------------------------------------------------------------

class _Scope:
    """One push/pop layer: an undo journal plus length markers.

    ``journal`` maps ``(kind, key)`` to the value the location held when it
    was first written inside this scope (``_ABSENT`` if it did not exist).
    Only the top scope journals, so ``push`` itself is O(1) and never
    copies the term graph.
    """

    __slots__ = ("journal", "n_terms", "n_inputs", "n_distincts")

    def __init__(self, n_terms, n_inputs, n_distincts):
        self.journal = {}
        self.n_terms = n_terms
        self.n_inputs = n_inputs
        self.n_distincts = n_distincts


class CongruenceClosure:
    """Proof-producing congruence closure over a shared term DAG."""

    def __init__(self, max_nodes=DEFAULT_MAX_NODES):
        if isinstance(max_nodes, bool) or not isinstance(max_nodes, int):
            raise ValidationError(
                f"max_nodes must be an int, got {type(max_nodes).__name__}")
        if max_nodes < 0:
            raise ValidationError(f"max_nodes must be >= 0, got {max_nodes}")
        self._max_nodes = max_nodes
        self._terms = []            # node id -> (func, tuple of arg ids)
        self._alive = []            # node id -> False once its scope popped
        self._live_count = 0        # number of currently valid nodes
        self._hashcons = {}         # (func, args) -> node id
        self._arity = {}            # func -> arity fixed at first use
        self._uf = []               # union-find parent links
        self._size = []             # union-find subtree sizes
        self._pf = []               # proof forest: None | (parent, reason)
        self._sig = {}              # (func, tuple of arg reps) -> node id
        self._class_parents = {}    # uf root -> [parent node ids]
        self._forbidden = {}        # uf root -> {other root: original pair}
        self._inputs = []           # asserted equalities, in order
        self._distincts = []        # asserted distinct pairs, in order
        self._scopes = []           # stack of _Scope frames

    # -- read-only views ----------------------------------------------------

    @property
    def max_nodes(self):
        return self._max_nodes

    @property
    def node_count(self):
        """Number of currently valid (live) nodes in the shared DAG."""
        return self._live_count

    @property
    def scope_depth(self):
        """Number of currently open assumption scopes (0 = base level)."""
        return len(self._scopes)

    @property
    def terms(self):
        """Tuple of ``(func, arg_ids)`` indexed by node id (a copy).

        Node ids are stable, so entries created inside a scope that was
        later popped remain as tombstones; they are rejected by every
        operation taking a node id (:class:`StaleNodeError`).
        """
        return tuple(self._terms)

    @property
    def input_equalities(self):
        """Asserted input equalities as a tuple of ``(a, b)`` pairs."""
        return tuple(self._inputs)

    @property
    def distinct_assertions(self):
        """Asserted distinct pairs as a tuple of ``(a, b)`` pairs."""
        return tuple(self._distincts)

    def term_of(self, nid):
        """Return ``(func, arg_ids)`` for node ``nid``."""
        self._check_node(nid, "term_of: nid")
        return self._terms[nid]

    def are_equal(self, a, b):
        """True iff terms ``a`` and ``b`` are equal in the current closure."""
        self._check_node(a, "are_equal: a")
        self._check_node(b, "are_equal: b")
        return self._find(a) == self._find(b)

    # -- validation ----------------------------------------------------------

    def _check_node(self, nid, where):
        if isinstance(nid, bool):
            raise ValidationError(
                f"{where}: node id must be an int, not bool ({nid!r})")
        if not isinstance(nid, int):
            raise ValidationError(
                f"{where}: node id must be an int, got "
                f"{type(nid).__name__} ({nid!r})")
        if nid < 0 or nid >= len(self._terms):
            raise UnknownNodeError(
                f"{where}: unknown node id {nid}; valid range is "
                f"0..{len(self._terms) - 1}")
        if not self._alive[nid]:
            raise StaleNodeError(
                f"{where}: node id {nid} was created in a scope that has "
                f"been popped; the handle is no longer valid")

    # -- scope journal ---------------------------------------------------------

    def _journal(self, kind, key, old_value):
        """Record ``old_value`` for ``(kind, key)`` in the top scope.

        Only the first write of a location within a scope is recorded, so
        replaying the journal restores exactly the state at ``push``.
        """
        if self._scopes:
            self._scopes[-1].journal.setdefault((kind, key), old_value)

    def _journal_idx(self, kind, arr, i):
        if self._scopes:
            self._scopes[-1].journal.setdefault((kind, i), arr[i])

    def _journal_sig(self, sig):
        if self._scopes:
            self._journal("sig", sig, self._sig.get(sig, _ABSENT))

    def _journal_parents(self, root):
        if self._scopes:
            lst = self._class_parents.get(root)
            self._journal("cp", root, _ABSENT if lst is None else lst[:])

    def _journal_forbidden(self, root):
        if self._scopes:
            d = self._forbidden.get(root)
            self._journal("frb", root, _ABSENT if d is None else dict(d))

    # -- union-find ----------------------------------------------------------

    def _find(self, x):
        uf = self._uf
        root = x
        while uf[root] != root:
            root = uf[root]
        while uf[x] != root:
            nxt = uf[x]
            self._journal_idx("uf", uf, x)
            uf[x] = root
            x = nxt
        return root

    # -- proof forest ---------------------------------------------------------

    def _flip_to_root(self, x):
        """Reverse proof-forest edges so that ``x`` becomes its tree root."""
        chain = []
        cur = x
        while self._pf[cur] is not None:
            parent, reason = self._pf[cur]
            chain.append((cur, parent, reason))
            cur = parent
        for node, parent, reason in reversed(chain):
            self._journal_idx("pf", self._pf, parent)
            self._pf[parent] = (node, reason)
        self._journal_idx("pf", self._pf, x)
        self._pf[x] = None

    # -- snapshots (atomic operations / batch rollback) ----------------------

    def _snapshot(self):
        return (
            self._uf[:],
            self._size[:],
            self._pf[:],
            dict(self._sig),
            {root: lst[:] for root, lst in self._class_parents.items()},
            {root: dict(d) for root, d in self._forbidden.items()},
            list(self._inputs),
            list(self._distincts),
            len(self._terms),
            dict(self._hashcons),
            dict(self._arity),
            self._live_count,
        )

    def _restore(self, snap):
        (self._uf, self._size, self._pf, self._sig, self._class_parents,
         self._forbidden, self._inputs, self._distincts, nterms,
         self._hashcons, self._arity, self._live_count) = snap
        del self._terms[nterms:]
        del self._alive[nterms:]

    # -- term construction ----------------------------------------------------

    def add_term(self, func, args=()):
        """Add ``func(*args)`` to the shared DAG and return its node id.

        Structurally identical terms are hash-consed to the same id.  The
        arity of a function symbol is fixed by its first use.  Adding a term
        may itself trigger congruence merges; such merges are atomic with
        the addition.
        """
        if not isinstance(func, str) or func == "":
            raise ValidationError(
                f"add_term: func must be a non-empty str, got {func!r}")
        if not isinstance(args, (list, tuple)):
            raise ValidationError(
                f"add_term: args must be a list or tuple of node ids, got "
                f"{type(args).__name__}")
        arg_tuple = tuple(args)
        for i, a in enumerate(arg_tuple):
            self._check_node(a, f"add_term: args[{i}]")
        arity = self._arity.get(func)
        if arity is not None and arity != len(arg_tuple):
            raise ArityError(
                f"add_term: function {func!r} was fixed to arity {arity}, "
                f"got {len(arg_tuple)} argument(s)")
        key = (func, arg_tuple)
        existing = self._hashcons.get(key)
        if existing is not None:
            return existing
        if self._live_count >= self._max_nodes:
            raise NodeLimitError(
                f"add_term: node limit {self._max_nodes} reached; "
                f"cannot add {func!r}")
        snap = self._snapshot()
        try:
            nid = len(self._terms)
            self._terms.append(key)
            self._alive.append(True)
            self._live_count += 1
            self._journal("hc", key, _ABSENT)
            self._hashcons[key] = nid
            if func not in self._arity:
                self._journal("ar", func, _ABSENT)
                self._arity[func] = len(arg_tuple)
            self._uf.append(nid)
            self._size.append(1)
            self._pf.append(None)
            self._journal("cp", nid, _ABSENT)
            self._class_parents[nid] = []
            for a in dict.fromkeys(arg_tuple):
                root = self._find(a)
                self._journal_parents(root)
                self._class_parents[root].append(nid)
            sig = (func, tuple(self._find(a) for a in arg_tuple))
            other = self._sig.get(sig)
            if other is None:
                self._journal_sig(sig)
                self._sig[sig] = nid
            else:
                self._merge(nid, other, (_CONG, nid, other))
        except _Conflict as conflict:
            error = self._make_contradiction(
                conflict.pair, edge=conflict.edge)
            self._restore(snap)
            raise error from None
        return nid

    # -- merging --------------------------------------------------------------

    def _merge(self, a, b, reason):
        """Merge the classes of ``a`` and ``b``; propagate congruences."""
        work = [(a, b, reason)]
        while work:
            a, b, reason = work.pop()
            ra, rb = self._find(a), self._find(b)
            if ra == rb:
                continue
            fa = self._forbidden.get(ra)
            if fa is not None and rb in fa:
                raise _Conflict(fa[rb], (a, b, reason))
            fb = self._forbidden.get(rb)
            if fb is not None and ra in fb:
                raise _Conflict(fb[ra], (a, b, reason))
            if self._size[ra] > self._size[rb]:
                ra, rb = rb, ra
            # Proof forest: link the two trees with the reason edge a -- b.
            self._flip_to_root(a)
            self._journal_idx("pf", self._pf, a)
            self._pf[a] = (b, reason)
            self._journal_idx("uf", self._uf, ra)
            self._uf[ra] = rb
            self._journal_idx("size", self._size, rb)
            self._size[rb] += self._size[ra]
            self._merge_forbidden(ra, rb)
            # Recompute signatures of parents of the merged-away class.
            self._journal_parents(ra)
            for p in self._class_parents.pop(ra, ()):
                fp, argsp = self._terms[p]
                sigp = (fp, tuple(self._find(x) for x in argsp))
                q = self._sig.get(sigp)
                if q is not None and self._find(q) != self._find(p):
                    work.append((p, q, (_CONG, p, q)))
                else:
                    self._journal_sig(sigp)
                    self._sig[sigp] = p
                self._journal_parents(rb)
                self._class_parents[rb].append(p)

    def _merge_forbidden(self, ra, rb):
        """Merge forbidden sets after root ``ra`` was attached under ``rb``."""
        self._journal_forbidden(ra)
        self._journal_forbidden(rb)
        fa = self._forbidden.pop(ra, None)
        fb = self._forbidden.setdefault(rb, {})
        if not fa:
            if not fb:
                self._forbidden.pop(rb, None)
            return
        for other, pair in fa.items():
            fb.setdefault(other, pair)
            od = self._forbidden.get(other)
            if od is not None:
                self._journal_forbidden(other)
                od.pop(ra, None)
                od.setdefault(rb, pair)

    def _forbid(self, a, b):
        ra, rb = self._find(a), self._find(b)
        self._journal_forbidden(ra)
        self._journal_forbidden(rb)
        self._forbidden.setdefault(ra, {})[rb] = (a, b)
        self._forbidden.setdefault(rb, {})[ra] = (a, b)

    # -- assertions ------------------------------------------------------------

    def _make_contradiction(self, pair, edge=None, extra_distinct=()):
        """Build a ContradictionError for distinct pair ``(x, y)``.

        ``edge`` is the pending merge ``(a, b, reason)`` that would equate
        the two classes (None when the pair is already equal, e.g. a
        distinct assertion against already-equal terms).
        """
        x, y = pair
        memo = {}
        if edge is None:
            eq_proof = self._explain_chain(x, y, memo)
        else:
            a, b, reason = edge
            # x and a are in one class, y and b in the other (or swapped).
            if self._find(x) == self._find(a):
                left, right = x, y
            else:
                left, right = y, x
            eq_proof = (
                self._explain_chain(left, a, memo)
                + (self._expand(reason, memo),)
                + self._explain_chain(b, right, memo)
            )
        proof = (_CONTRADICTION, eq_proof, (x, y))
        distincts = {_norm_pair(p, q) for p, q in self._distincts}
        distincts.update(_norm_pair(p, q) for p, q in extra_distinct)
        return ContradictionError(
            f"terms {x} and {y} were asserted distinct but are equal",
            proof=proof,
            inputs=frozenset(_norm_pair(p, q) for p, q in self._inputs),
            distincts=frozenset(distincts),
            terms=tuple(self._terms),
        )

    def _assert_equal_inner(self, a, b):
        if self._find(a) == self._find(b):
            return
        self._inputs.append((a, b))
        try:
            self._merge(a, b, (_INPUT, a, b))
        except _Conflict as conflict:
            raise self._make_contradiction(
                conflict.pair, edge=conflict.edge) from None

    def assert_equal(self, a, b):
        """Assert ``a = b`` and close under congruence.

        Atomic: if the assertion contradicts a distinct pair, a
        :class:`ContradictionError` carrying a verifiable proof is raised
        and the structure is left exactly as before the call.
        """
        self._check_node(a, "assert_equal: a")
        self._check_node(b, "assert_equal: b")
        snap = self._snapshot()
        try:
            self._assert_equal_inner(a, b)
        except ContradictionError:
            self._restore(snap)
            raise

    def _assert_distinct_inner(self, a, b):
        if self._find(a) == self._find(b):
            raise self._make_contradiction((a, b), extra_distinct=((a, b),))
        self._distincts.append((a, b))
        self._forbid(a, b)

    def assert_distinct(self, a, b):
        """Assert ``a != b``.

        Raises :class:`ContradictionError` (with proof) if ``a`` and ``b``
        are already equal.  Otherwise records the constraint; any later
        merge that would equate them fails atomically.
        """
        self._check_node(a, "assert_distinct: a")
        self._check_node(b, "assert_distinct: b")
        self._assert_distinct_inner(a, b)

    def apply_batch(self, ops):
        """Apply a batch of assertions atomically.

        ``ops`` is an iterable of ``("=", a, b)`` / ``("!=", a, b)`` triples.
        If any assertion conflicts, the whole batch is rolled back and the
        :class:`ContradictionError` (with proof) is re-raised; no partial
        change is left behind.
        """
        ops_list = list(ops)
        for i, op in enumerate(ops_list):
            if not isinstance(op, (tuple, list)) or len(op) != 3:
                raise ValidationError(
                    f"apply_batch: op {i} must be a ('='|'!=', a, b) triple, "
                    f"got {op!r}")
            if op[0] not in ("=", "!="):
                raise ValidationError(
                    f"apply_batch: op {i} has unknown relation {op[0]!r}; "
                    f"expected '=' or '!='")
            self._check_node(op[1], f"apply_batch: op {i} left operand")
            self._check_node(op[2], f"apply_batch: op {i} right operand")
        snap = self._snapshot()
        try:
            for rel, a, b in ops_list:
                if rel == "=":
                    self._assert_equal_inner(a, b)
                else:
                    self._assert_distinct_inner(a, b)
        except ContradictionError:
            self._restore(snap)
            raise

    # -- scoped assumptions (push/pop) -----------------------------------------

    def push(self):
        """Open a new assumption scope and return the new scope depth.

        Everything asserted or built until the matching :meth:`pop` --
        equalities, distinct assertions and newly created terms -- belongs
        to this scope.  Inner scopes may freely reference outer terms.
        ``push`` is O(1): nothing is copied; mutations are recorded in a
        per-scope change journal instead.
        """
        self._scopes.append(
            _Scope(len(self._terms), len(self._inputs), len(self._distincts)))
        return len(self._scopes)

    def pop(self):
        """Leave the innermost scope, undoing everything asserted in it.

        Equivalence classes, parent signatures, the proof forest and the
        conflict (distinct) state return to exactly what they were at the
        matching :meth:`push`.  Terms created inside the scope keep their
        (never reused) ids but become invalid: passing one to any operation
        raises :class:`StaleNodeError`, and a structurally identical term
        built afterwards gets a fresh id.  A scope whose last operation
        failed with :class:`ContradictionError` can still be popped.
        Raises :class:`ScopeError` at the base level.
        """
        if not self._scopes:
            raise ScopeError("pop: already at base level; no scope to leave")
        scope = self._scopes.pop()
        # Replay the journal: restore every location first written inside
        # this scope to the value it held at push time.
        for (kind, key), old in scope.journal.items():
            if kind == "uf":
                self._uf[key] = old
            elif kind == "size":
                self._size[key] = old
            elif kind == "pf":
                self._pf[key] = old
            elif kind == "sig":
                if old is _ABSENT:
                    self._sig.pop(key, None)
                else:
                    self._sig[key] = old
            elif kind == "hc":
                self._hashcons.pop(key, None)
            elif kind == "ar":
                self._arity.pop(key, None)
            elif kind == "cp":
                if old is _ABSENT:
                    self._class_parents.pop(key, None)
                else:
                    self._class_parents[key] = old
            elif kind == "frb":
                if old is _ABSENT:
                    self._forbidden.pop(key, None)
                else:
                    self._forbidden[key] = old
        # Tombstone the terms created in the scope: their ids stay reserved
        # (never reused) but every handle to them is invalid from now on.
        # The uf/size/pf arrays keep their (now unreachable) entries so
        # that node ids stay aligned with array indices.
        n = scope.n_terms
        newly_dead = 0
        for i in range(n, len(self._terms)):
            if self._alive[i]:
                self._alive[i] = False
                newly_dead += 1
        self._live_count -= newly_dead
        # Truncate the assertion lists to their length at push time.
        del self._inputs[scope.n_inputs:]
        del self._distincts[scope.n_distincts:]

    @contextlib.contextmanager
    def scope(self):
        """Context manager wrapping :meth:`push`/:meth:`pop`.

        The scope is popped when the ``with`` block exits, even if an
        operation inside it raised (e.g. :class:`ContradictionError`).
        Do not call :meth:`pop` manually inside the block.
        """
        self.push()
        try:
            yield self
        finally:
            self.pop()

    # -- explanation ------------------------------------------------------------

    def explain(self, a, b):
        """Return a verifiable proof that ``a = b``.

        The proof is a tuple of edge proofs forming a chain from ``a`` to
        ``b``; each edge is ``("input", x, y)`` or
        ``("cong", t1, t2, (subproof_per_argument, ...))``.  Raises
        :class:`NotEqualError` if the terms are not equal.
        """
        self._check_node(a, "explain: a")
        self._check_node(b, "explain: b")
        if self._find(a) != self._find(b):
            raise NotEqualError(
                f"explain: terms {a} and {b} are not equal; "
                f"no equality proof exists")
        _ensure_recursion_limit(4 * len(self._terms) + 100)
        return self._explain_chain(a, b, {})

    def _explain_chain(self, a, b, memo):
        if a == b:
            return ()
        key = _norm_pair(a, b)
        cached = memo.get(key)
        if cached is not None:
            return cached
        # Ancestors of a in the proof forest (root included, mapped to None).
        anc = {}
        cur = a
        while True:
            entry = self._pf[cur]
            anc[cur] = entry
            if entry is None:
                break
            cur = entry[0]
        # Walk from b to the nearest common ancestor.
        lca = b
        while lca not in anc:
            lca = self._pf[lca][0]
        chain = []
        cur = a
        while cur != lca:
            parent, reason = self._pf[cur]
            chain.append(reason)
            cur = parent
        back = []
        cur = b
        while cur != lca:
            parent, reason = self._pf[cur]
            back.append(reason)
            cur = parent
        chain.extend(reversed(back))
        proof = tuple(self._expand(reason, memo) for reason in chain)
        memo[key] = proof
        return proof

    def _expand(self, reason, memo):
        if reason[0] == _INPUT:
            return (_INPUT, reason[1], reason[2])
        _, p, q = reason
        _, args_p = self._terms[p]
        _, args_q = self._terms[q]
        subs = tuple(
            self._explain_chain(x, y, memo) for x, y in zip(args_p, args_q))
        return (_CONG, p, q, subs)


# ---------------------------------------------------------------------------
# Independent proof verification
# ---------------------------------------------------------------------------

def _check_proof_id(nid, terms, where):
    if isinstance(nid, bool) or not isinstance(nid, int):
        raise ProofError(
            f"{where}: node id must be an int, got "
            f"{type(nid).__name__} ({nid!r})")
    if nid < 0 or nid >= len(terms):
        raise ProofError(f"{where}: unknown node id {nid}")


def _verify_chain(proof, start, input_set, terms, where):
    if not isinstance(proof, tuple):
        raise ProofError(f"{where}: proof chain must be a tuple")
    cur = start
    for i, edge in enumerate(proof):
        cur = _verify_edge(edge, cur, input_set, terms, f"{where}[{i}]")
    return cur


def _verify_edge(edge, cur, input_set, terms, where):
    if not isinstance(edge, tuple) or not edge:
        raise ProofError(f"{where}: edge must be a non-empty tuple")
    kind = edge[0]
    if kind == _INPUT:
        if len(edge) != 3:
            raise ProofError(f"{where}: input edge must have 3 elements")
        _, x, y = edge
        _check_proof_id(x, terms, where)
        _check_proof_id(y, terms, where)
        if _norm_pair(x, y) not in input_set:
            raise ProofError(
                f"{where}: ({x}, {y}) is not an asserted input equality")
        if cur == x:
            return y
        if cur == y:
            return x
        raise ProofError(
            f"{where}: input edge ({x}, {y}) does not continue the chain "
            f"at {cur}")
    if kind == _CONG:
        if len(edge) != 4:
            raise ProofError(f"{where}: congruence edge must have 4 elements")
        _, t1, t2, subs = edge
        _check_proof_id(t1, terms, where)
        _check_proof_id(t2, terms, where)
        f1, args1 = terms[t1]
        f2, args2 = terms[t2]
        if f1 != f2:
            raise ProofError(
                f"{where}: congruence needs the same function symbol, got "
                f"{f1!r} and {f2!r}")
        if not isinstance(subs, tuple) or len(subs) != len(args1):
            raise ProofError(
                f"{where}: expected {len(args1)} argument subproof(s), got "
                f"{subs!r}")
        if cur == t1:
            nxt = t2
        elif cur == t2:
            nxt = t1
        else:
            raise ProofError(
                f"{where}: congruence edge ({t1}, {t2}) does not continue "
                f"the chain at {cur}")
        for k, (x, y, sub) in enumerate(zip(args1, args2, subs)):
            end = _verify_chain(sub, x, input_set, terms, f"{where}.arg{k}")
            if end != y:
                raise ProofError(
                    f"{where}.arg{k}: subproof ends at {end}, expected {y}")
        return nxt
    raise ProofError(f"{where}: unknown edge kind {kind!r}")


def verify_proof(proof, a, b, inputs, terms):
    """Independently verify that ``proof`` derives ``a = b``.

    ``inputs`` is the set of asserted input equalities (pairs of node ids)
    the proof may appeal to; ``terms`` maps node ids to ``(func, args)``.
    Returns ``True`` on success, raises :class:`ProofError` (locating the
    failing step) otherwise.
    """
    terms = tuple(terms)
    _check_proof_id(a, terms, "verify_proof: a")
    _check_proof_id(b, terms, "verify_proof: b")
    _ensure_recursion_limit(4 * len(terms) + 100)
    input_set = set()
    for pair in inputs:
        if not isinstance(pair, (tuple, list)) or len(pair) != 2:
            raise ProofError(
                f"verify_proof: input equality must be a pair, got {pair!r}")
        x, y = pair
        _check_proof_id(x, terms, "verify_proof: inputs")
        _check_proof_id(y, terms, "verify_proof: inputs")
        input_set.add(_norm_pair(x, y))
    end = _verify_chain(proof, a, input_set, terms, "proof")
    if end != b:
        raise ProofError(f"proof chain ends at {end}, expected {b}")
    return True


def verify_contradiction(proof, inputs, distincts, terms):
    """Independently verify a contradiction proof.

    ``proof`` must be ``("contradiction", equality_proof, (x, y))`` where
    ``(x, y)`` is one of the asserted ``distincts`` and ``equality_proof``
    derives ``x = y`` from ``inputs``.  Returns ``True`` or raises
    :class:`ProofError`.
    """
    terms = tuple(terms)
    if not (isinstance(proof, tuple) and len(proof) == 3
            and proof[0] == _CONTRADICTION):
        raise ProofError(
            "contradiction proof must be ('contradiction', eq_proof, (x, y))")
    _, eq_proof, pair = proof
    if not isinstance(pair, (tuple, list)) or len(pair) != 2:
        raise ProofError(f"contradiction pair must be a pair, got {pair!r}")
    x, y = pair
    _check_proof_id(x, terms, "verify_contradiction: pair")
    _check_proof_id(y, terms, "verify_contradiction: pair")
    distinct_set = set()
    for d in distincts:
        if not isinstance(d, (tuple, list)) or len(d) != 2:
            raise ProofError(
                f"verify_contradiction: distinct entry must be a pair, "
                f"got {d!r}")
        distinct_set.add(_norm_pair(d[0], d[1]))
    if _norm_pair(x, y) not in distinct_set:
        raise ProofError(
            f"({x}, {y}) is not among the asserted distinct pairs")
    verify_proof(eq_proof, x, y, inputs, terms)
    return True


# ---------------------------------------------------------------------------
# Pretty printing helpers
# ---------------------------------------------------------------------------

def term_to_str(nid, terms, _memo=None):
    """Render node ``nid`` as a term string such as ``f(g(a), b)``."""
    if _memo is None:
        _memo = {}
    cached = _memo.get(nid)
    if cached is not None:
        return cached
    _ensure_recursion_limit(4 * len(terms) + 100)
    func, args = terms[nid]
    if not args:
        text = func
    else:
        text = f"{func}(" + ", ".join(
            term_to_str(a, terms, _memo) for a in args) + ")"
    _memo[nid] = text
    return text


def proof_to_str(proof, terms):
    """Render an equality (or contradiction) proof as numbered steps."""
    _ensure_recursion_limit(4 * len(terms) + 100)
    lines = []

    def emit_chain(chain, indent):
        for edge in chain:
            if edge[0] == _INPUT:
                lines.append(
                    f"{indent}input: {term_to_str(edge[1], terms)}"
                    f" = {term_to_str(edge[2], terms)}")
            else:
                _, t1, t2, subs = edge
                lines.append(
                    f"{indent}congruence: {term_to_str(t1, terms)}"
                    f" = {term_to_str(t2, terms)}")
                for k, sub in enumerate(subs):
                    if sub:
                        lines.append(f"{indent}  argument {k}:")
                        emit_chain(sub, indent + "    ")

    if (isinstance(proof, tuple) and len(proof) == 3
            and proof[0] == _CONTRADICTION):
        _, eq_proof, (x, y) = proof
        lines.append(
            f"contradiction: {term_to_str(x, terms)} and "
            f"{term_to_str(y, terms)} were asserted distinct, but:")
        emit_chain(eq_proof, "  ")
    else:
        emit_chain(proof, "")
    return "\n".join(lines)
