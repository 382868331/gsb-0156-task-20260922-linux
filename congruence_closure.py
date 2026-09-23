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
* a boolean layer (:class:`BooleanSolver`) adds AND / OR / NOT formulas over
  at most ``MAX_BOOLEAN_ATOMS`` (8) equality/inequality atoms.  Satisfiability
  is decided by truth-table enumeration (at most 256 candidates); each
  candidate is checked in a fresh congruence closure rebuilt from the shared
  template DAG, true atoms asserted as equalities and false atoms ("opposite
  equalities") as distinctness constraints, giving absolute branch isolation.

Standard library only.  Python 3.14.7.
"""

from __future__ import annotations

import sys

__all__ = [
    "DEFAULT_MAX_NODES",
    "MAX_BOOLEAN_ATOMS",
    "CongruenceClosure",
    "BooleanSolver",
    "SatResult",
    "CongruenceError",
    "ValidationError",
    "ArityError",
    "UnknownNodeError",
    "NodeLimitError",
    "AtomLimitError",
    "NotEqualError",
    "ContradictionError",
    "ProofError",
    "verify_proof",
    "verify_contradiction",
    "term_to_str",
    "proof_to_str",
    "land",
    "lor",
    "lnot",
]

DEFAULT_MAX_NODES = 5000
MAX_BOOLEAN_ATOMS = 8

_INPUT = "input"
_CONG = "cong"
_CONTRADICTION = "contradiction"

_AND = "and"
_OR = "or"
_NOT = "not"


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


class NodeLimitError(CongruenceError):
    """The shared DAG already holds ``max_nodes`` nodes."""


class AtomLimitError(CongruenceError):
    """A boolean problem uses more than ``MAX_BOOLEAN_ATOMS`` atoms."""


class NotEqualError(CongruenceError):
    """``explain`` was asked to prove an equality that does not hold.

    The closure algorithm is complete and terminating, so this is a
    definitive "no proof exists", not an exhausted search budget.  The only
    resource bound in this module is the node limit (:class:`NodeLimitError`).
    """


class ProofError(CongruenceError):
    """A proof failed independent verification; the message locates the step."""


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

    # -- read-only views ----------------------------------------------------

    @property
    def max_nodes(self):
        return self._max_nodes

    @property
    def node_count(self):
        return len(self._terms)

    @property
    def terms(self):
        """Tuple of ``(func, arg_ids)`` indexed by node id (a copy)."""
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

    # -- union-find ----------------------------------------------------------

    def _find(self, x):
        uf = self._uf
        root = x
        while uf[root] != root:
            root = uf[root]
        while uf[x] != root:
            uf[x], x = root, uf[x]
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
            self._pf[parent] = (node, reason)
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
        )

    def _restore(self, snap):
        (self._uf, self._size, self._pf, self._sig, self._class_parents,
         self._forbidden, self._inputs, self._distincts, nterms,
         self._hashcons, self._arity) = snap
        del self._terms[nterms:]

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
        if len(self._terms) >= self._max_nodes:
            raise NodeLimitError(
                f"add_term: node limit {self._max_nodes} reached; "
                f"cannot add {func!r}")
        snap = self._snapshot()
        try:
            nid = len(self._terms)
            self._terms.append(key)
            self._hashcons[key] = nid
            self._arity.setdefault(func, len(arg_tuple))
            self._uf.append(nid)
            self._size.append(1)
            self._pf.append(None)
            self._class_parents[nid] = []
            for a in dict.fromkeys(arg_tuple):
                self._class_parents[self._find(a)].append(nid)
            sig = (func, tuple(self._find(a) for a in arg_tuple))
            other = self._sig.get(sig)
            if other is None:
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
            self._pf[a] = (b, reason)
            self._uf[ra] = rb
            self._size[rb] += self._size[ra]
            self._merge_forbidden(ra, rb)
            # Recompute signatures of parents of the merged-away class.
            for p in self._class_parents.pop(ra, ()):
                fp, argsp = self._terms[p]
                sigp = (fp, tuple(self._find(x) for x in argsp))
                q = self._sig.get(sigp)
                if q is not None and self._find(q) != self._find(p):
                    work.append((p, q, (_CONG, p, q)))
                else:
                    self._sig[sigp] = p
                self._class_parents[rb].append(p)

    def _merge_forbidden(self, ra, rb):
        """Merge forbidden sets after root ``ra`` was attached under ``rb``."""
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
                od.pop(ra, None)
                od.setdefault(rb, pair)

    def _forbid(self, a, b):
        ra, rb = self._find(a), self._find(b)
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
# Boolean layer: AND / OR / NOT over equality/inequality atoms
# ---------------------------------------------------------------------------
#
# A formula is a plain nested tuple (cheap to build, easy to inspect):
#
#   atom                 -- non-negative int, an atom index (0-based);
#   ("not", p)           -- negation;
#   ("and", p1, p2, ...) -- conjunction (one or more children);
#   ("or",  p1, p2, ...) -- disjunction (one or more children).
#
# Atom *i* stands for the equality ``a_i = b_i`` registered with
# :meth:`BooleanSolver.add_atom`; its negation is the inequality
# ``a_i != b_i``.  At most ``MAX_BOOLEAN_ATOMS`` (8) atoms are allowed.
#
# Satisfiability is decided by truth-table enumeration (at most 2**8 = 256
# assignments).  Each candidate assignment is tested in a *fresh*
# CongruenceClosure whose term DAG is rebuilt from the shared template DAG
# (shared subterms hash-cons again inside the candidate): true atoms are
# asserted as equalities, false atoms as distinctness constraints.  Branch
# isolation is therefore absolute -- a contradictory candidate never leaks
# state into the others or into the solver.


def land(*children):
    """Construct an ``("and", ...)`` formula node."""
    return (_AND,) + tuple(children)


def lor(*children):
    """Construct an ``("or", ...)`` formula node."""
    return (_OR,) + tuple(children)


def lnot(child):
    """Construct a ``("not", child)`` formula node."""
    return (_NOT, child)


class SatResult:
    """Outcome of :meth:`BooleanSolver.solve`.

    * ``satisfiable`` -- bool;
    * ``assignment``  -- tuple of bools aligned with the solver's atoms when
      satisfiable (``assignment[i]`` is the truth value of atom *i*), else
      ``None``;
    * ``assignments`` -- tuple of every satisfying assignment when
      ``solve(..., find_all=True)``, else a one-element tuple (or empty).
    """

    __slots__ = ("satisfiable", "assignment", "assignments")

    def __init__(self, assignments):
        self.assignments = tuple(assignments)
        self.satisfiable = bool(self.assignments)
        self.assignment = self.assignments[0] if self.assignments else None

    def __bool__(self):
        return self.satisfiable

    def __repr__(self):
        if self.satisfiable:
            return f"SatResult(sat, assignment={self.assignment!r})"
        return "SatResult(unsat)"


class BooleanSolver:
    """Enumerative SAT over equality/inequality atoms on top of the kernel.

    The solver owns a *template* :class:`CongruenceClosure` in which terms
    are registered with :meth:`add_term` and atoms with :meth:`add_atom`.
    The template is never asserted into: :meth:`solve` rebuilds a fresh
    closure for every candidate assignment, so the solver stays reusable
    across calls and a contradictory candidate cannot leave partial state.
    """

    def __init__(self, max_nodes=DEFAULT_MAX_NODES):
        # Delegate validation of max_nodes to the kernel constructor.
        self._template = CongruenceClosure(max_nodes=max_nodes)
        self._atoms = []            # [(a, b)] in registration order
        self._atom_index = {}       # normalized pair -> atom index

    # -- read-only views ----------------------------------------------------

    @property
    def max_nodes(self):
        return self._template.max_nodes

    @property
    def atom_count(self):
        return len(self._atoms)

    @property
    def atom_pairs(self):
        """Tuple of registered atom pairs ``(a, b)``, registration order."""
        return tuple(self._atoms)

    @property
    def terms(self):
        """Tuple ``(func, arg_ids)`` of the template DAG, indexed by id."""
        return self._template.terms

    # -- term / atom registration -------------------------------------------

    def add_term(self, func, args=()):
        """Add a term to the template DAG (delegates to the kernel)."""
        return self._template.add_term(func, args)

    def add_atom(self, a, b):
        """Register the equality atom ``a = b`` and return its index.

        The symmetric pair is deduplicated (``(a, b)`` and ``(b, a)`` are
        the same atom).  At most :data:`MAX_BOOLEAN_ATOMS` atoms may be
        registered; exceeding the bound raises :class:`AtomLimitError`.
        """
        self._template._check_node(a, "add_atom: a")
        self._template._check_node(b, "add_atom: b")
        key = _norm_pair(a, b)
        existing = self._atom_index.get(key)
        if existing is not None:
            return existing
        if len(self._atoms) >= MAX_BOOLEAN_ATOMS:
            raise AtomLimitError(
                f"add_atom: at most {MAX_BOOLEAN_ATOMS} boolean atoms are "
                f"allowed, already have {len(self._atoms)}")
        idx = len(self._atoms)
        self._atoms.append(key)
        self._atom_index[key] = idx
        return idx

    # -- formula validation --------------------------------------------------

    def _validate_formula(self, root, where):
        # Iterative over an explicit stack so arbitrarily deep nesting is
        # reported as a located ValidationError, never a RecursionError.
        stack = [(root, where)]
        while stack:
            node, pos = stack.pop()
            if isinstance(node, bool) or not isinstance(node, int):
                if not isinstance(node, (tuple, list)):
                    raise ValidationError(
                        f"{pos}: formula node must be an atom index (int) or "
                        f"a tagged tuple, got {node!r}")
                if not node:
                    raise ValidationError(
                        f"{pos}: formula tuple must have a tag as first "
                        f"element")
                tag = node[0]
                if not isinstance(tag, str) or tag not in (_AND, _OR, _NOT):
                    raise ValidationError(
                        f"{pos}: unknown connective {tag!r}; expected 'and', "
                        f"'or' or 'not'")
                children = node[1:]
                if tag == _NOT:
                    if len(children) != 1:
                        raise ValidationError(
                            f"{pos}: 'not' takes exactly 1 child, got "
                            f"{len(children)}")
                elif not children:
                    raise ValidationError(
                        f"{pos}: {tag!r} takes at least 1 child")
                for i, child in reversed(list(enumerate(children))):
                    stack.append((child, f"{pos}.{tag}[{i}]"))
            elif node < 0 or node >= len(self._atoms):
                raise ValidationError(
                    f"{pos}: atom index {node} out of range; solver has "
                    f"{len(self._atoms)} atom(s)")

    # -- evaluation and candidate construction -------------------------------

    @staticmethod
    def _eval(root, bits):
        # Iterative post-order evaluation (formula depth is not bounded by
        # the 8-atom limit).
        stack = [(root, False)]
        values = []
        while stack:
            node, processed = stack.pop()
            if isinstance(node, int) and not isinstance(node, bool):
                values.append(bits[node])
                continue
            tag = node[0]
            if not processed:
                stack.append((node, True))
                if tag == _NOT:
                    stack.append((node[1], False))
                else:
                    for child in reversed(node[1:]):
                        stack.append((child, False))
            elif tag == _NOT:
                values.append(not values.pop())
            elif tag == _AND:
                result = True
                for _ in node[1:]:
                    result = values.pop() and result
                values.append(result)
            else:
                result = False
                for _ in node[1:]:
                    result = values.pop() or result
                values.append(result)
        return values[0]

    def _rebuild(self, bits):
        """Rebuild a fresh kernel closure with the signed literals of bits.

        Returns the closure on success, or ``None`` when the assignment is
        inconsistent (a :class:`ContradictionError` from the kernel).
        """
        cc = CongruenceClosure(max_nodes=self._template.max_nodes)
        mapping = {}
        for old, (func, old_args) in enumerate(self._template.terms):
            args = tuple(mapping[x] for x in old_args)
            mapping[old] = cc.add_term(func, args)
        try:
            for i, (a, b) in enumerate(self._atoms):
                x, y = mapping[a], mapping[b]
                if bits[i]:
                    cc.assert_equal(x, y)
                else:
                    cc.assert_distinct(x, y)
        except ContradictionError:
            return None
        return cc

    # -- solving --------------------------------------------------------------

    def solve(self, formula, *, find_all=False):
        """Enumerate assignments satisfying ``formula``.

        Returns a :class:`SatResult`.  Enumeration order is deterministic:
        atom 0 is the least-significant bit of the candidate mask, so the
        all-false assignment is tried first.  Each candidate is tested in a
        rebuilt, fully isolated equality environment.
        """
        self._validate_formula(formula, "solve: formula")
        n = len(self._atoms)
        found = []
        for mask in range(1 << n):
            bits = tuple(bool((mask >> i) & 1) for i in range(n))
            if not self._eval(formula, bits):
                continue
            if self._rebuild(bits) is None:
                continue
            found.append(bits)
            if not find_all:
                break
        return SatResult(found)

    def all_models(self, formula):
        """Return the tuple of every satisfying assignment of ``formula``."""
        return self.solve(formula, find_all=True).assignments

    def build_environment(self, assignment):
        """Rebuild the kernel closure for one (satisfying) assignment.

        Useful after :meth:`solve` for further equality queries against the
        model (``are_equal``, ``explain``, ...).  Raises
        :class:`ContradictionError` if the assignment is itself
        inconsistent with congruence.
        """
        if not isinstance(assignment, (tuple, list)):
            raise ValidationError(
                f"build_environment: assignment must be a tuple/list of bool, "
                f"got {type(assignment).__name__}")
        if len(assignment) != len(self._atoms):
            raise ValidationError(
                f"build_environment: assignment length {len(assignment)} "
                f"does not match atom count {len(self._atoms)}")
        bits = []
        for i, v in enumerate(assignment):
            if not isinstance(v, bool):
                raise ValidationError(
                    f"build_environment: assignment[{i}] must be bool, got "
                    f"{type(v).__name__} ({v!r})")
            bits.append(v)
        cc = self._rebuild(tuple(bits))
        if cc is None:
            raise ContradictionError(
                "assignment is inconsistent with the equality theory "
                "(a false atom is forced equal or a true atom is distinct)",
                proof=None, inputs=frozenset(), distincts=frozenset(),
                terms=self._template.terms)
        return cc


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
