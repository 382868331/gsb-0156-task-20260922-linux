"""Tests for boolean_solver.

Expected values are hand-computed or produced by an independent oracle in
this file: a brute-force all-pairs equivalence closure for theory
consistency plus a structural formula evaluator.  The module under test
is never used to generate expected values.
"""

import os
import random
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from congruence_closure import (  # noqa: E402
    NodeLimitError,
    UnknownNodeError,
    ValidationError,
)
from boolean_solver import (  # noqa: E402
    MAX_ATOMS,
    SAT,
    UNSAT,
    And,
    Atom,
    AtomLimitError,
    BooleanSolver,
    Not,
    Or,
)


# ---------------------------------------------------------------------------
# Independent oracle (never calls boolean_solver's solving machinery)
# ---------------------------------------------------------------------------

def oracle_closure(terms, equalities):
    """Brute-force all-pairs fixed point of equality + congruence."""
    parent = list(range(len(terms)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry

    for a, b in equalities:
        union(a, b)
    changed = True
    while changed:
        changed = False
        for i in range(len(terms)):
            fi, ai = terms[i]
            for j in range(i + 1, len(terms)):
                fj, aj = terms[j]
                if fi != fj or len(ai) != len(aj) or find(i) == find(j):
                    continue
                if all(find(x) == find(y) for x, y in zip(ai, aj)):
                    union(i, j)
                    changed = True
    return find


def oracle_consistent(terms, equalities, distincts):
    """True iff no distinct pair is merged by the closure of equalities."""
    find = oracle_closure(terms, equalities)
    return all(find(x) != find(y) for x, y in distincts)


def eval_formula(formula, values):
    """Structural evaluation of the boolean skeleton."""
    if isinstance(formula, Atom):
        return values[formula.atom_id]
    if isinstance(formula, Not):
        return not eval_formula(formula.child, values)
    if isinstance(formula, And):
        return all(eval_formula(c, values) for c in formula.children)
    if isinstance(formula, Or):
        return any(eval_formula(c, values) for c in formula.children)
    raise AssertionError(f"not a formula: {formula!r}")


def collect_atom_ids(formula):
    if isinstance(formula, Atom):
        return {formula.atom_id}
    if isinstance(formula, Not):
        return collect_atom_ids(formula.child)
    ids = set()
    for child in formula.children:
        ids |= collect_atom_ids(child)
    return ids


def oracle_status(solver, formula):
    """Expected SAT/UNSAT by full enumeration against the oracle."""
    atom_ids = sorted(collect_atom_ids(formula))
    atoms = solver.atoms  # public data view only
    for mask in range(1 << len(atom_ids)):
        values = {aid: bool((mask >> i) & 1)
                  for i, aid in enumerate(atom_ids)}
        if not eval_formula(formula, values):
            continue
        equalities, distincts = [], []
        for aid in atom_ids:
            pair = (atoms[aid].a, atoms[aid].b)
            (equalities if values[aid] else distincts).append(pair)
        if oracle_consistent(solver.terms, equalities, distincts):
            return SAT
    return UNSAT


def check_assignment_against_oracle(testcase, solver, formula, result):
    """A SAT assignment must satisfy the skeleton and be consistent."""
    values = {atom.atom_id: value
              for atom, value in result.assignment.items()}
    testcase.assertTrue(eval_formula(formula, values))
    equalities, distincts = [], []
    for atom, value in result.assignment.items():
        (equalities if value else distincts).append((atom.a, atom.b))
    testcase.assertTrue(
        oracle_consistent(solver.terms, equalities, distincts))


# ---------------------------------------------------------------------------
# Hand-computed cases
# ---------------------------------------------------------------------------

class TestBasicSolving(unittest.TestCase):
    def setUp(self):
        self.solver = BooleanSolver()
        self.a = self.solver.add_term("a")
        self.b = self.solver.add_term("b")
        self.c = self.solver.add_term("c")

    def test_single_equality_sat(self):
        e = self.solver.eq(self.a, self.b)
        result = self.solver.solve(e)
        self.assertEqual(result.status, SAT)
        self.assertTrue(result.satisfiable)
        self.assertEqual(result.assignment, {e: True})
        self.assertEqual(result.environments_tested, 1)

    def test_disequality_entry_sat(self):
        e = self.solver.eq(self.a, self.b)
        result = self.solver.solve(self.solver.ne(self.a, self.b))
        self.assertEqual(result.status, SAT)
        self.assertEqual(result.assignment, {e: False})

    def test_reflexive_disequality_unsat(self):
        # ne(a, a) is Not(eq(a, a)); a = a always holds, so UNSAT.
        result = self.solver.solve(self.solver.ne(self.a, self.a))
        self.assertEqual(result.status, UNSAT)
        self.assertFalse(result.satisfiable)
        self.assertIsNone(result.assignment)

    def test_and_or_not_hand_computed(self):
        # (e1 OR e2) AND NOT e1  <=>  (NOT e1) AND e2
        e1 = self.solver.eq(self.a, self.b)
        e2 = self.solver.eq(self.b, self.c)
        result = self.solver.solve(And(Or(e1, e2), Not(e1)))
        self.assertEqual(result.status, SAT)
        self.assertEqual(result.assignment, {e1: False, e2: True})

    def test_transitivity_unsat(self):
        # a = b AND b = c AND a != c: boolean-satisfying only with
        # (True, True, False), which transitivity forbids.
        e_ab = self.solver.eq(self.a, self.b)
        e_bc = self.solver.eq(self.b, self.c)
        formula = And(e_ab, e_bc, self.solver.ne(self.a, self.c))
        result = self.solver.solve(formula)
        self.assertEqual(result.status, UNSAT)
        self.assertEqual(result.environments_tested, 1)

    def test_congruence_unsat(self):
        # a = b AND f(a) != f(b): congruence forces f(a) = f(b).
        fa = self.solver.add_term("f", [self.a])
        fb = self.solver.add_term("f", [self.b])
        formula = And(self.solver.eq(self.a, self.b),
                      self.solver.ne(fa, fb))
        result = self.solver.solve(formula)
        self.assertEqual(result.status, UNSAT)

    def test_tautology_sat(self):
        e = self.solver.eq(self.a, self.b)
        result = self.solver.solve(Or(e, Not(e)))
        self.assertEqual(result.status, SAT)

    def test_empty_connectives(self):
        # And() is the empty conjunction (true); Or() is empty (false).
        result = self.solver.solve(And())
        self.assertEqual(result.status, SAT)
        self.assertEqual(result.assignment, {})
        result = self.solver.solve(Or())
        self.assertEqual(result.status, UNSAT)
        self.assertEqual(result.environments_tested, 0)


class TestSharingAndIsolation(unittest.TestCase):
    def setUp(self):
        self.solver = BooleanSolver()
        self.a = self.solver.add_term("a")
        self.b = self.solver.add_term("b")
        self.c = self.solver.add_term("c")

    def test_shared_subterms(self):
        fa1 = self.solver.add_term("f", [self.a])
        fa2 = self.solver.add_term("f", [self.a])
        self.assertEqual(fa1, fa2)
        self.assertEqual(self.solver.node_count, 4)  # a, b, c, f(a)
        gfa = self.solver.add_term("g", [fa1])
        self.assertEqual(self.solver.terms[gfa], ("g", (fa1,)))

    def test_atom_sharing(self):
        e1 = self.solver.eq(self.a, self.b)
        e2 = self.solver.eq(self.b, self.a)  # argument order normalized
        self.assertIs(e1, e2)
        self.assertEqual(self.solver.atom_count, 1)
        self.solver.ne(self.a, self.b)  # disequality shares the atom
        self.assertEqual(self.solver.atom_count, 1)

    def test_solve_does_not_mutate_solver(self):
        e_ab = self.solver.eq(self.a, self.b)
        e_bc = self.solver.eq(self.b, self.c)
        before = (self.solver.node_count, self.solver.atom_count,
                  self.solver.terms)
        r1 = self.solver.solve(And(e_ab, e_bc))
        self.assertEqual((self.solver.node_count, self.solver.atom_count,
                          self.solver.terms), before)
        r2 = self.solver.solve(And(e_ab, e_bc))
        self.assertEqual(r1.status, r2.status)
        self.assertEqual(r1.assignment, r2.assignment)

    def test_opposite_equalities_branch_isolation(self):
        # Branch 1 (a=b, b=c, a!=c) is theory-inconsistent; branch 2
        # (a=b, b=c) is consistent.  The disequality asserted while
        # checking branch 1 must not leak into branch 2's environment.
        e_ab = self.solver.eq(self.a, self.b)
        e_bc = self.solver.eq(self.b, self.c)
        e_ac = self.solver.eq(self.a, self.c)
        branch1 = And(e_ab, e_bc, Not(e_ac))
        branch2 = And(e_ab, e_bc)
        result = self.solver.solve(Or(branch1, branch2))
        self.assertEqual(result.status, SAT)
        # Branch 1 fails its environment check first, branch 2 succeeds.
        self.assertEqual(result.environments_tested, 2)
        self.assertEqual(result.assignment, {e_ab: True, e_bc: True,
                                             e_ac: True})

    def test_isolation_across_solve_calls(self):
        # Asserting a = b SAT in one call must not make a != b UNSAT
        # in the next call.
        e = self.solver.eq(self.a, self.b)
        self.assertEqual(self.solver.solve(e).status, SAT)
        result = self.solver.solve(Not(e))
        self.assertEqual(result.status, SAT)
        self.assertEqual(result.assignment, {e: False})


class TestResultAndFormatting(unittest.TestCase):
    def test_format_assignment(self):
        solver = BooleanSolver()
        a = solver.add_term("a")
        b = solver.add_term("b")
        fa = solver.add_term("f", [a])
        e_ab = solver.eq(a, b)
        e_ff = solver.eq(fa, solver.add_term("f", [b]))
        result = solver.solve(And(e_ab, Not(e_ff)))
        # a = b forces f(a) = f(b), so the only consistent boolean
        # candidate is e_ab=True, e_ff=True -- but the formula demands
        # e_ff=False, hence UNSAT.
        self.assertEqual(result.status, UNSAT)
        self.assertEqual(solver.format_assignment(result), "unsat")

    def test_format_sat_assignment(self):
        solver = BooleanSolver()
        a = solver.add_term("a")
        b = solver.add_term("b")
        e = solver.eq(a, b)
        result = solver.solve(Not(e))
        self.assertEqual(solver.format_assignment(result), "a = b: False")

    def test_result_repr(self):
        solver = BooleanSolver()
        a = solver.add_term("a")
        result = solver.solve(solver.eq(a, a))
        self.assertIn("sat", repr(result))


class TestValidation(unittest.TestCase):
    def setUp(self):
        self.solver = BooleanSolver()
        self.a = self.solver.add_term("a")
        self.b = self.solver.add_term("b")

    def test_max_atoms_validation(self):
        for bad in (True, -1, MAX_ATOMS + 1, 2.5, "8"):
            with self.assertRaises(ValidationError):
                BooleanSolver(max_atoms=bad)

    def test_atom_limit_default_is_eight(self):
        solver = BooleanSolver()
        ids = [solver.add_term(f"v{i}") for i in range(9)]
        for i in range(8):
            solver.eq(ids[i], ids[i + 1])  # 8 distinct atoms: fine
        self.assertEqual(solver.atom_count, MAX_ATOMS)
        with self.assertRaises(AtomLimitError):
            solver.eq(ids[8], ids[0])  # 9th distinct atom rejected
        # No half-updated state: still exactly 8 atoms, solver usable.
        self.assertEqual(solver.atom_count, MAX_ATOMS)
        result = solver.solve(solver.eq(ids[0], ids[1]))
        self.assertEqual(result.status, SAT)

    def test_atom_limit_configurable(self):
        solver = BooleanSolver(max_atoms=1)
        x = solver.add_term("x")
        y = solver.add_term("y")
        z = solver.add_term("z")
        solver.eq(x, y)
        with self.assertRaises(AtomLimitError):
            solver.eq(y, z)
        self.assertEqual(solver.atom_count, 1)

    def test_eq_ne_node_validation(self):
        for bad in (True, 0.5, float("nan"), "a"):
            with self.assertRaises(ValidationError):
                self.solver.eq(self.a, bad)
            with self.assertRaises(ValidationError):
                self.solver.ne(bad, self.a)
        with self.assertRaises(UnknownNodeError):
            self.solver.eq(self.a, 99)
        with self.assertRaises(UnknownNodeError):
            self.solver.ne(-1, self.a)

    def test_connective_child_validation(self):
        with self.assertRaises(ValidationError):
            Not("x")
        with self.assertRaises(ValidationError) as ctx:
            And(self.solver.eq(self.a, self.b), 3)
        self.assertIn("child 1", str(ctx.exception))
        with self.assertRaises(ValidationError):
            Or(None)

    def test_solve_rejects_non_formula(self):
        for bad in ("a = b", 42, [self.solver.eq(self.a, self.b)]):
            with self.assertRaises(ValidationError):
                self.solver.solve(bad)

    def test_solve_rejects_foreign_atom(self):
        other = BooleanSolver()
        x = other.add_term("x")
        y = other.add_term("y")
        foreign = other.eq(x, y)
        before = self.solver.atom_count
        with self.assertRaises(ValidationError) as ctx:
            self.solver.solve(foreign)
        self.assertIn("different BooleanSolver", str(ctx.exception))
        self.assertEqual(self.solver.atom_count, before)

    def test_node_limit_propagates(self):
        solver = BooleanSolver(max_nodes=1)
        solver.add_term("a")
        with self.assertRaises(NodeLimitError):
            solver.add_term("b")


class TestOracleCrossCheck(unittest.TestCase):
    """Random small formulas checked against the independent oracle."""

    def build_random_formula(self, rng, atoms, depth):
        if depth == 0 or rng.random() < 0.4:
            formula = rng.choice(atoms)
            return Not(formula) if rng.random() < 0.3 else formula
        kind = rng.choice((And, Or, Not))
        if kind is Not:
            return Not(self.build_random_formula(rng, atoms, depth - 1))
        n = rng.randint(1, 3)
        return kind(*(self.build_random_formula(rng, atoms, depth - 1)
                      for _ in range(n)))

    def test_random_formulas_match_oracle(self):
        for seed in range(40):
            rng = random.Random(seed)
            solver = BooleanSolver()
            n_consts = rng.randint(2, 4)
            for i in range(n_consts):
                solver.add_term(f"c{i}")
            n_terms = rng.randint(0, 5)
            for _ in range(n_terms):
                func, arity = rng.choice((("f", 1), ("g", 2), ("h", 1)))
                args = [rng.randrange(solver.node_count)
                        for _ in range(arity)]
                solver.add_term(func, args)
            n_atoms = rng.randint(1, 6)
            atoms = []
            for _ in range(n_atoms):
                x = rng.randrange(solver.node_count)
                y = rng.randrange(solver.node_count)
                atom = solver.eq(x, y)
                if atom not in atoms:
                    atoms.append(atom)
            formula = self.build_random_formula(rng, atoms, depth=3)
            result = solver.solve(formula)
            expected = oracle_status(solver, formula)
            self.assertEqual(result.status, expected,
                             f"seed={seed} formula={formula!r}")
            if result.status == SAT:
                check_assignment_against_oracle(self, solver, formula,
                                                result)


if __name__ == "__main__":
    unittest.main()
