"""Boolean combinations of (dis)equalities over the congruence-closure kernel.

Adds and/or/not connectives and a disequality entry point on top of
:mod:`congruence_closure`:

* atoms are equality literals ``eq(a, b)`` over terms of a shared,
  hash-consed term store (:meth:`BooleanSolver.add_term`); ``ne(a, b)``
  is the disequality entry point, shorthand for ``Not(eq(a, b))``, and
  shares the same atom;
* a solver tracks at most ``MAX_ATOMS`` (8) distinct boolean atoms, so
  satisfiability is decided by enumerating all truth assignments
  (at most ``2**8 == 256``) and rebuilding a fresh
  :class:`~congruence_closure.CongruenceClosure` equality environment per
  candidate branch -- branches are fully isolated from each other and
  from the shared term store, and ``solve`` never mutates the solver;
* :meth:`BooleanSolver.solve` returns a :class:`SolveResult` with status
  ``SAT`` (plus the satisfying assignment) or ``UNSAT``.

Standard library only.  Python 3.14.7.
"""

from __future__ import annotations

from congruence_closure import (
    DEFAULT_MAX_NODES,
    CongruenceClosure,
    CongruenceError,
    ContradictionError,
    UnknownNodeError,
    ValidationError,
    term_to_str,
)

__all__ = [
    "MAX_ATOMS",
    "SAT",
    "UNSAT",
    "AtomLimitError",
    "Formula",
    "Atom",
    "Not",
    "And",
    "Or",
    "SolveResult",
    "BooleanSolver",
]

MAX_ATOMS = 8

SAT = "sat"
UNSAT = "unsat"


# ---------------------------------------------------------------------------
# Errors
# ---------------------------------------------------------------------------

class AtomLimitError(CongruenceError):
    """The solver already tracks ``max_atoms`` distinct boolean atoms."""


# ---------------------------------------------------------------------------
# Formula tree
# ---------------------------------------------------------------------------

class Formula:
    """Base class of boolean formulas over equality atoms."""

    __slots__ = ()


class Atom(Formula):
    """An equality literal ``a = b`` over two term-store node ids.

    Atoms are created by :meth:`BooleanSolver.eq`; structurally identical
    literals (in either argument order) share one ``Atom`` object.
    """

    __slots__ = ("_solver", "_id", "_a", "_b")

    def __init__(self, solver, atom_id, a, b):
        self._solver = solver
        self._id = atom_id
        self._a = a
        self._b = b

    @property
    def atom_id(self):
        """Solver-local id of this atom (0-based, in creation order)."""
        return self._id

    @property
    def a(self):
        """Left operand node id (normalized: ``a <= b``)."""
        return self._a

    @property
    def b(self):
        """Right operand node id (normalized: ``a <= b``)."""
        return self._b

    def __repr__(self):
        return f"eq({self._a}, {self._b})"


def _check_child(child, where):
    if not isinstance(child, Formula):
        raise ValidationError(
            f"{where}: expected a Formula (Atom, Not, And or Or), got "
            f"{type(child).__name__} ({child!r})")


class Not(Formula):
    """Boolean negation of a formula."""

    __slots__ = ("child",)

    def __init__(self, child):
        _check_child(child, "Not: child")
        self.child = child

    def __repr__(self):
        return f"Not({self.child!r})"


class _Connective(Formula):
    __slots__ = ("children",)
    _name = "?"

    def __init__(self, *children):
        for i, child in enumerate(children):
            _check_child(child, f"{self._name}: child {i}")
        self.children = tuple(children)

    def __repr__(self):
        inner = ", ".join(repr(c) for c in self.children)
        return f"{self._name}({inner})"


class And(_Connective):
    """Boolean conjunction; ``And()`` is the empty conjunction (true)."""

    _name = "And"


class Or(_Connective):
    """Boolean disjunction; ``Or()`` is the empty disjunction (false)."""

    _name = "Or"


# ---------------------------------------------------------------------------
# Solve result
# ---------------------------------------------------------------------------

class SolveResult:
    """Outcome of :meth:`BooleanSolver.solve`.

    * ``status`` -- ``SAT`` or ``UNSAT`` (the module constants);
    * ``assignment`` -- for ``SAT``, a dict mapping each :class:`Atom` of
      the formula to its truth value; ``None`` for ``UNSAT``;
    * ``environments_tested`` -- how many candidate assignments passed the
      boolean evaluation and had their equality environment rebuilt and
      checked for theory consistency.
    """

    __slots__ = ("status", "assignment", "environments_tested")

    def __init__(self, status, assignment, environments_tested):
        self.status = status
        self.assignment = assignment
        self.environments_tested = environments_tested

    @property
    def satisfiable(self):
        """True iff ``status`` is ``SAT``."""
        return self.status == SAT

    def __repr__(self):
        return (f"SolveResult(status={self.status!r}, "
                f"environments_tested={self.environments_tested})")


# ---------------------------------------------------------------------------
# Solver
# ---------------------------------------------------------------------------

class BooleanSolver:
    """And/or/not over (dis)equality atoms, decided by enumeration.

    Terms live in one shared, hash-consed store (subterms are shared
    across all atoms and all candidate branches).  ``solve`` enumerates
    truth assignments to the formula's atoms; each candidate that
    satisfies the boolean skeleton is checked by rebuilding a fresh
    :class:`CongruenceClosure` environment from the shared term table,
    so no assertion ever leaks between branches or into the solver.
    """

    def __init__(self, max_atoms=MAX_ATOMS, max_nodes=DEFAULT_MAX_NODES):
        if isinstance(max_atoms, bool) or not isinstance(max_atoms, int):
            raise ValidationError(
                f"max_atoms must be an int, got {type(max_atoms).__name__}")
        if max_atoms < 0 or max_atoms > MAX_ATOMS:
            raise ValidationError(
                f"max_atoms must be between 0 and {MAX_ATOMS}, "
                f"got {max_atoms}")
        self._max_atoms = max_atoms
        self._store = CongruenceClosure(max_nodes=max_nodes)
        self._atoms = []          # atom id -> Atom
        self._atom_by_pair = {}   # normalized (a, b) -> Atom

    # -- read-only views ----------------------------------------------------

    @property
    def max_atoms(self):
        return self._max_atoms

    @property
    def max_nodes(self):
        return self._store.max_nodes

    @property
    def node_count(self):
        return self._store.node_count

    @property
    def atom_count(self):
        return len(self._atoms)

    @property
    def atoms(self):
        """Tuple of the solver's atoms, indexed by atom id."""
        return tuple(self._atoms)

    @property
    def terms(self):
        """Tuple of ``(func, arg_ids)`` indexed by node id (a copy)."""
        return self._store.terms

    # -- validation ----------------------------------------------------------

    def _check_node(self, nid, where):
        if isinstance(nid, bool):
            raise ValidationError(
                f"{where}: node id must be an int, not bool ({nid!r})")
        if not isinstance(nid, int):
            raise ValidationError(
                f"{where}: node id must be an int, got "
                f"{type(nid).__name__} ({nid!r})")
        if nid < 0 or nid >= self._store.node_count:
            raise UnknownNodeError(
                f"{where}: unknown node id {nid}; valid range is "
                f"0..{self._store.node_count - 1}")

    # -- term and atom construction ------------------------------------------

    def add_term(self, func, args=()):
        """Add ``func(*args)`` to the shared term store, return its node id.

        Same contract as :meth:`CongruenceClosure.add_term`: structural
        sharing (hash-consing), arity fixed at first use, ``max_nodes``
        bound.  The store holds no assertions, so additions never merge.
        """
        return self._store.add_term(func, args)

    def eq(self, a, b):
        """Return the atom for the equality literal ``a = b``.

        The same literal (in either argument order) always returns the
        same :class:`Atom`.  Creating a *new* atom beyond ``max_atoms``
        raises :class:`AtomLimitError` and leaves the solver unchanged.
        """
        self._check_node(a, "eq: a")
        self._check_node(b, "eq: b")
        key = (a, b) if a <= b else (b, a)
        atom = self._atom_by_pair.get(key)
        if atom is None:
            if len(self._atoms) >= self._max_atoms:
                raise AtomLimitError(
                    f"eq: atom limit {self._max_atoms} reached; cannot "
                    f"add a new atom for ({a}, {b})")
            atom = Atom(self, len(self._atoms), key[0], key[1])
            self._atoms.append(atom)
            self._atom_by_pair[key] = atom
        return atom

    def ne(self, a, b):
        """Disequality entry point: ``Not(eq(a, b))`` on the shared atom."""
        self._check_node(a, "ne: a")
        self._check_node(b, "ne: b")
        return Not(self.eq(a, b))

    # -- solving --------------------------------------------------------------

    def solve(self, formula):
        """Decide whether ``formula`` is satisfiable.

        Enumerates truth assignments to the formula's atoms (at most
        ``2**max_atoms``).  Each assignment satisfying the boolean
        skeleton is checked by rebuilding a fresh equality environment
        (``True`` atoms become ``assert_equal``, ``False`` atoms become
        ``assert_distinct``); the first consistent one is returned as a
        ``SAT`` :class:`SolveResult`.  If none is consistent, the result
        is ``UNSAT``.  The solver itself is never mutated.
        """
        atom_ids = sorted(self._check_formula(formula, "solve: formula"))
        n = len(atom_ids)
        environments_tested = 0
        for mask in range(1 << n):
            values = {aid: bool((mask >> i) & 1)
                      for i, aid in enumerate(atom_ids)}
            if not _eval_formula(formula, values):
                continue
            environments_tested += 1
            if self._consistent(atom_ids, values):
                assignment = {self._atoms[aid]: values[aid]
                              for aid in atom_ids}
                return SolveResult(SAT, assignment, environments_tested)
        return SolveResult(UNSAT, None, environments_tested)

    def _check_formula(self, formula, where):
        """Validate the formula tree; return the set of atom ids used."""
        if isinstance(formula, Atom):
            if formula._solver is not self:
                raise ValidationError(
                    f"{where}: atom {formula!r} belongs to a different "
                    f"BooleanSolver")
            return {formula.atom_id}
        if isinstance(formula, Not):
            return self._check_formula(formula.child, f"{where} (in Not)")
        if isinstance(formula, (And, Or)):
            kind = type(formula).__name__
            ids = set()
            for i, child in enumerate(formula.children):
                ids |= self._check_formula(
                    child, f"{where} ({kind} child {i})")
            return ids
        raise ValidationError(
            f"{where}: expected a Formula (Atom, Not, And or Or), got "
            f"{type(formula).__name__} ({formula!r})")

    def _consistent(self, atom_ids, values):
        """Rebuild a fresh equality environment for one assignment."""
        env = CongruenceClosure(max_nodes=self._store.max_nodes)
        # Re-adding the shared term table in creation order reproduces
        # the same node ids (hash-consing is deterministic and no
        # assertions exist yet, so nothing merges).
        for func, args in self._store.terms:
            env.add_term(func, args)
        try:
            for aid in atom_ids:
                atom = self._atoms[aid]
                if values[aid]:
                    env.assert_equal(atom.a, atom.b)
                else:
                    env.assert_distinct(atom.a, atom.b)
        except ContradictionError:
            return False
        return True

    # -- presentation ----------------------------------------------------------

    def atom_to_str(self, atom):
        """Render an atom as ``f(a) = b`` using the shared term table."""
        if not isinstance(atom, Atom) or atom._solver is not self:
            raise ValidationError(
                f"atom_to_str: not an atom of this solver ({atom!r})")
        terms = self._store.terms
        return (f"{term_to_str(atom.a, terms)} = "
                f"{term_to_str(atom.b, terms)}")

    def format_assignment(self, result):
        """Render a SAT result's assignment as ``t1 = t2: True; ...``."""
        if not isinstance(result, SolveResult):
            raise ValidationError(
                f"format_assignment: expected a SolveResult, got "
                f"{type(result).__name__} ({result!r})")
        if result.status != SAT:
            return UNSAT
        parts = []
        for atom in sorted(result.assignment, key=lambda at: at.atom_id):
            parts.append(
                f"{self.atom_to_str(atom)}: {result.assignment[atom]}")
        return "; ".join(parts)


def _eval_formula(formula, values):
    """Evaluate the boolean skeleton under an atom-id -> bool mapping."""
    if isinstance(formula, Atom):
        return values[formula.atom_id]
    if isinstance(formula, Not):
        return not _eval_formula(formula.child, values)
    if isinstance(formula, And):
        return all(_eval_formula(c, values) for c in formula.children)
    return any(_eval_formula(c, values) for c in formula.children)
