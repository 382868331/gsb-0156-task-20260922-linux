"""Tests for the boolean layer (BooleanSolver) in congruence_closure.

Expected values come from independent references implemented here:

* ``ref_consistent`` -- naive union + all-pairs congruence fixed point over
  the raw term table, then a check that every false atom is a distinct
  pair; it never instantiates the kernel;
* ``ref_formula_eval`` -- an independent, stack-based formula evaluator.

Random instances cross-check the *whole* set of satisfying assignments.
"""

import os
import random
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from congruence_closure import (  # noqa: E402
    MAX_BOOLEAN_ATOMS,
    AtomLimitError,
    BooleanSolver,
    ContradictionError,
    UnknownNodeError,
    ValidationError,
    land,
    lnot,
    lor,
)


# ---------------------------------------------------------------------------
# Independent references
# ---------------------------------------------------------------------------

def ref_consistent(bits, terms, atoms):
    """True iff the assignment `bits` admits a model of equality + distinct.

    Equalities (true atoms) feed a naive congruence fixed point; every
    false atom must end in a different equivalence class.
    """
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

    for i, (a, b) in enumerate(atoms):
        if bits[i]:
            union(a, b)
    changed = True
    while changed:
        changed = False
        for i in range(len(terms)):
            fi, ai = terms[i]
            for j in range(i + 1, len(terms)):
                fj, aj = terms[j]
                if fi != fj or find(i) == find(j):
                    continue
                if all(find(x) == find(y) for x, y in zip(ai, aj)):
                    union(i, j)
                    changed = True
    for i, (a, b) in enumerate(atoms):
        if not bits[i] and find(a) == find(b):
            return False
    return True


def ref_formula_eval(node, values):
    """Evaluate a formula with atom values in the dict/list `values`."""
    stack = [(node, False)]
    value_stack = []
    while stack:
        cur, processed = stack.pop()
        if isinstance(cur, int) and not isinstance(cur, bool):
            value_stack.append(bool(values[cur]))
            continue
        tag = cur[0]
        if not processed:
            stack.append((cur, True))
            if tag == "not":
                stack.append((cur[1], False))
            else:
                for child in reversed(cur[1:]):
                    stack.append((child, False))
        else:
            if tag == "not":
                value_stack.append(not value_stack.pop())
            elif tag == "and":
                results = [value_stack.pop() for _ in cur[1:]]
                value_stack.append(all(results))
            else:
                results = [value_stack.pop() for _ in cur[1:]]
                value_stack.append(any(results))
    return value_stack[0]


def ref_models(terms, atoms, formula):
    n = len(atoms)
    models = []
    for mask in range(1 << n):
        bits = tuple(bool((mask >> i) & 1) for i in range(n))
        if (ref_formula_eval(formula, bits)
                and ref_consistent(bits, terms, atoms)):
            models.append(bits)
    return tuple(models)


def make_random_problem(rng, n_atoms):
    sol = BooleanSolver()
    terms = []
    n_consts = rng.randint(2, 4)
    for i in range(n_consts):
        nid = sol.add_term(f"c{i}")
        terms.append((f"c{i}", ()))
    funcs = [("f", 1), ("g", 2)]
    for _ in range(rng.randint(2, 6)):
        f, ar = rng.choice(funcs)
        args = tuple(rng.randrange(len(terms)) for _ in range(ar))
        nid = sol.add_term(f, args)
        if nid == len(terms):
            terms.append((f, args))
    atoms = []
    n = len(terms)
    seen = set()
    while len(atoms) < n_atoms:
        a, b = rng.randrange(n), rng.randrange(n)
        key = (a, b) if a <= b else (b, a)
        if key in seen:
            continue
        seen.add(key)
        sol.add_atom(a, b)
        atoms.append(key)

    def make_formula(depth):
        if depth == 0 or rng.random() < 0.35:
            return rng.randrange(n_atoms)
        op = rng.choice(["and", "or", "not"])
        if op == "not":
            return ("not", make_formula(depth - 1))
        k = rng.randint(2, 3)
        return (op,) + tuple(make_formula(depth - 1) for _ in range(k))

    formula = make_formula(3)
    return sol, terms, atoms, formula


# ---------------------------------------------------------------------------
# Normal behavior
# ---------------------------------------------------------------------------

class TestBooleanBasic(unittest.TestCase):
    def test_pure_positive_atom(self):
        sol = BooleanSolver()
        a, b = sol.add_term("a"), sol.add_term("b")
        p = sol.add_atom(a, b)
        result = sol.solve(p)
        self.assertTrue(result.satisfiable)
        self.assertEqual(result.assignment, (True,))
        self.assertEqual(result.assignments, ((True,),))

    def test_negated_atom(self):
        sol = BooleanSolver()
        a, b = sol.add_term("a"), sol.add_term("b")
        sol.add_atom(a, b)
        result = sol.solve(("not", 0))
        self.assertTrue(result)
        self.assertEqual(result.assignment, (False,))

    def test_transitive_conjunction_and_environment(self):
        sol = BooleanSolver()
        a, b, c = (sol.add_term(n) for n in "abc")
        p = sol.add_atom(a, b)
        q = sol.add_atom(b, c)
        result = sol.solve(land(p, q))
        self.assertTrue(result)
        self.assertEqual(result.assignment, (True, True))
        cc = sol.build_environment(result.assignment)
        self.assertTrue(cc.are_equal(a, c))

    def test_disjunction_two_models(self):
        # (a = b) or (a = c), but not both: exactly two models.
        sol = BooleanSolver()
        a, b, c = (sol.add_term(n) for n in "abc")
        p = sol.add_atom(a, b)
        q = sol.add_atom(a, c)
        formula = land(lor(p, q), lnot(land(p, q)))
        models = sol.all_models(formula)
        self.assertEqual(set(models), {(True, False), (False, True)})

    def test_congruence_makes_branch_unsat(self):
        # a = b AND f(a) != f(b) is unsatisfiable (congruence).
        sol = BooleanSolver()
        a, b = sol.add_term("a"), sol.add_term("b")
        fa, fb = sol.add_term("f", [a]), sol.add_term("f", [b])
        p = sol.add_atom(a, b)
        q = sol.add_atom(fa, fb)
        result = sol.solve(land(p, lnot(q)))
        self.assertFalse(result.satisfiable)
        self.assertIsNone(result.assignment)
        self.assertEqual(result.assignments, ())

    def test_congruence_is_one_way_under_branch(self):
        # f(a) = f(b) AND a != b IS satisfiable: congruence never reverses.
        sol = BooleanSolver()
        a, b = sol.add_term("a"), sol.add_term("b")
        fa, fb = sol.add_term("f", [a]), sol.add_term("f", [b])
        p = sol.add_atom(a, b)
        q = sol.add_atom(fa, fb)
        result = sol.solve(land(q, lnot(p)))
        self.assertTrue(result)
        self.assertEqual(result.assignment, (False, True))
        cc = sol.build_environment(result.assignment)
        self.assertTrue(cc.are_equal(fa, fb))
        self.assertFalse(cc.are_equal(a, b))

    def test_deep_congruence_propagation_inside_branch(self):
        sol = BooleanSolver()
        a, b = sol.add_term("a"), sol.add_term("b")
        ta, tb = a, b
        for _ in range(50):
            ta, tb = sol.add_term("f", [ta]), sol.add_term("f", [tb])
        p = sol.add_atom(a, b)
        q = sol.add_atom(ta, tb)
        # The only consistent truth tables make p and q equivalent.
        self.assertEqual(set(sol.all_models(land(p, lnot(q)))), set())
        self.assertTrue(sol.solve(land(p, q)))
        self.assertTrue(sol.solve(land(lnot(p), lnot(q))))

    def test_contradictory_formula_p_and_not_p(self):
        sol = BooleanSolver()
        a, b = sol.add_term("a"), sol.add_term("b")
        sol.add_atom(a, b)
        self.assertFalse(sol.solve(land(0, lnot(0))))

    def test_helper_constructors(self):
        self.assertEqual(land(0, 1), ("and", 0, 1))
        self.assertEqual(lor(0, 1), ("or", 0, 1))
        self.assertEqual(lnot(0), ("not", 0))


class TestBooleanSharedSubterms(unittest.TestCase):
    def test_shared_subterms_rebuilt_once(self):
        # g(f(a)) appears in two atoms; the candidate closure shares it.
        sol = BooleanSolver()
        a, b = sol.add_term("a"), sol.add_term("b")
        fa = sol.add_term("f", [a])
        gfa = sol.add_term("g", [fa])
        fb = sol.add_term("f", [b])
        gfb = sol.add_term("g", [fb])
        p = sol.add_atom(fa, fb)
        q = sol.add_atom(gfa, gfb)
        # f(a)=f(b) and g(f(a))!=g(f(b)) cannot coexist.
        self.assertFalse(sol.solve(land(p, lnot(q))))
        # Rebuilt DAG has the same nodes as the template.
        cc = sol.build_environment((True, True))
        self.assertEqual(cc.node_count, len(sol.terms))
        self.assertEqual(cc.node_count, 6)


class TestBooleanEnumerationOrder(unittest.TestCase):
    def test_first_model_is_lowest_mask(self):
        sol = BooleanSolver()
        a, b, c = (sol.add_term(n) for n in "abc")
        sol.add_atom(a, b)
        sol.add_atom(b, c)
        # Formula satisfied by exactly (True, False) and (False, True);
        # atom 0 is the least-significant bit, so mask 0b01 = (True, False)
        # is enumerated first.
        formula = lor(land(0, lnot(1)), land(lnot(0), 1))
        result = sol.solve(formula)
        self.assertEqual(result.assignment, (True, False))
        self.assertEqual(set(sol.all_models(formula)),
                         {(False, True), (True, False)})


# ---------------------------------------------------------------------------
# Boundary cases
# ---------------------------------------------------------------------------

class TestBooleanBoundaries(unittest.TestCase):
    def test_eight_atoms_allowed_ninth_rejected(self):
        sol = BooleanSolver()
        consts = [sol.add_term(f"c{i}") for i in range(9)]
        for i in range(MAX_BOOLEAN_ATOMS):
            self.assertEqual(sol.add_atom(consts[i], consts[i + 1]), i)
        self.assertEqual(sol.atom_count, MAX_BOOLEAN_ATOMS)
        with self.assertRaises(AtomLimitError):
            sol.add_atom(consts[0], consts[8])

    def test_eight_atom_full_truth_table_runs(self):
        sol = BooleanSolver()
        consts = [sol.add_term(f"c{i}") for i in range(8)]
        # Seven adjacent-chain atoms plus one endpoint atom: 8 atoms total.
        for i in range(7):
            sol.add_atom(consts[i], consts[i + 1])
        sol.add_atom(consts[0], consts[7])
        # All eight true: consistent chain.
        result = sol.solve(land(*range(MAX_BOOLEAN_ATOMS)))
        self.assertTrue(result)
        self.assertEqual(result.assignment, (True,) * 8)
        # The seven adjacent equalities force c0 = c7, so the endpoint
        # distinctness (negated atom 7) is unsatisfiable.
        formula = land(*range(7), lnot(7))
        self.assertFalse(sol.solve(formula))
        # Enumerating all models of the disjunction touches every truth
        # table row; cross-check the exact count with the independent
        # reference rather than hand-counting.
        formula = lor(*range(MAX_BOOLEAN_ATOMS))
        models = sol.all_models(formula)
        terms = sol.terms
        expected = set(ref_models(terms, sol.atom_pairs, formula))
        self.assertEqual(set(models), expected)
        # All-false falsifies the OR and is not among the models.
        self.assertNotIn((False,) * 8, expected)


    def test_symmetric_atom_deduplicated(self):
        sol = BooleanSolver()
        a, b = sol.add_term("a"), sol.add_term("b")
        self.assertEqual(sol.add_atom(a, b), 0)
        self.assertEqual(sol.add_atom(b, a), 0)
        self.assertEqual(sol.atom_count, 1)
        self.assertEqual(sol.atom_pairs, ((a, b),))

    def test_reflexive_atom(self):
        # a = a is forced true; the negated literal a != a is impossible.
        sol = BooleanSolver()
        a = sol.add_term("a")
        sol.add_atom(a, a)
        self.assertTrue(sol.solve(0))
        self.assertFalse(sol.solve(("not", 0)))

    def test_unused_atom_still_enumerated(self):
        sol = BooleanSolver()
        a, b, c = (sol.add_term(n) for n in "abc")
        sol.add_atom(a, b)
        sol.add_atom(b, c)
        # Formula ignores atom 1: both its values give models.
        models = set(sol.all_models(0))
        self.assertEqual(models, {(True, True), (True, False)})


# ---------------------------------------------------------------------------
# Branch isolation / state hygiene
# ---------------------------------------------------------------------------

class TestBooleanIsolation(unittest.TestCase):
    def setUp(self):
        self.sol = BooleanSolver()
        a, b = self.sol.add_term("a"), self.sol.add_term("b")
        self.a, self.b = a, b
        self.fa = self.sol.add_term("f", [a])
        self.fb = self.sol.add_term("f", [b])
        self.p = self.sol.add_atom(a, b)
        self.q = self.sol.add_atom(self.fa, self.fb)

    def test_unsat_solve_leaves_no_state_and_is_repeatable(self):
        terms_before = self.sol.terms
        formula = land(self.p, lnot(self.q))  # unsat
        r1 = self.sol.solve(formula)
        r2 = self.sol.solve(formula)
        self.assertFalse(r1)
        self.assertFalse(r2)
        self.assertEqual(self.sol.terms, terms_before)
        self.assertEqual(self.sol.atom_count, 2)
        # A different, satisfiable query still works afterwards.
        self.assertTrue(self.sol.solve(land(self.q, lnot(self.p))))

    def test_solve_is_deterministic_across_calls(self):
        formula = lor(self.p, self.q)
        self.assertEqual(self.sol.solve(formula).assignment,
                         self.sol.solve(formula).assignment)
        self.assertEqual(self.sol.all_models(formula),
                         self.sol.all_models(formula))

    def test_candidate_contradiction_does_not_poison_next_candidate(self):
        # Enumeration hits the unsat (True, False) candidate before the
        # sat (True, True) one; ordering must not leak the contradiction.
        result = self.sol.solve(land(self.p, self.q))
        self.assertEqual(result.assignment, (True, True))


class TestBuildEnvironment(unittest.TestCase):
    def test_inconsistent_assignment_raises(self):
        sol = BooleanSolver()
        a, b = sol.add_term("a"), sol.add_term("b")
        fa, fb = sol.add_term("f", [a]), sol.add_term("f", [b])
        sol.add_atom(a, b)
        sol.add_atom(fa, fb)
        with self.assertRaises(ContradictionError):
            sol.build_environment((True, False))

    def test_bad_assignment_shape(self):
        sol = BooleanSolver()
        a, b = sol.add_term("a"), sol.add_term("b")
        sol.add_atom(a, b)
        with self.assertRaises(ValidationError):
            sol.build_environment((True, True))
        with self.assertRaises(ValidationError):
            sol.build_environment((1,))
        with self.assertRaises(ValidationError):
            sol.build_environment("x")


# ---------------------------------------------------------------------------
# Validation failures
# ---------------------------------------------------------------------------

class TestBooleanValidation(unittest.TestCase):
    def setUp(self):
        self.sol = BooleanSolver()
        self.a = self.sol.add_term("a")
        self.b = self.sol.add_term("b")
        self.sol.add_atom(self.a, self.b)

    def test_bad_atom_operands(self):
        with self.assertRaises(ValidationError):
            self.sol.add_atom(self.a, True)
        with self.assertRaises(UnknownNodeError):
            self.sol.add_atom(self.a, 99)
        with self.assertRaises(ValidationError):
            self.sol.add_atom(0.0, self.b)

    def test_atom_index_out_of_range(self):
        with self.assertRaises(ValidationError):
            self.sol.solve(1)
        with self.assertRaises(ValidationError):
            self.sol.solve(-1)

    def test_unknown_connective(self):
        with self.assertRaises(ValidationError) as ctx:
            self.sol.solve(("xor", 0, 0))
        self.assertIn("xor", str(ctx.exception))

    def test_not_arity(self):
        with self.assertRaises(ValidationError):
            self.sol.solve(("not",))
        with self.assertRaises(ValidationError):
            self.sol.solve(("not", 0, 0))

    def test_and_or_need_children(self):
        with self.assertRaises(ValidationError):
            self.sol.solve(("and",))
        with self.assertRaises(ValidationError):
            self.sol.solve(("or",))

    def test_non_formula_node(self):
        for bad in (1.5, "atom", None, {"not": 0}, (), (0,)):
            with self.assertRaises(ValidationError):
                self.sol.solve(bad)

    def test_error_locates_nested_path(self):
        with self.assertRaises(ValidationError) as ctx:
            self.sol.solve(("and", 0, ("or", ("not", 9))))
        self.assertIn("and[1]", str(ctx.exception))
        self.assertIn("not", str(ctx.exception))

    def test_nested_bad_node_deep(self):
        with self.assertRaises(ValidationError):
            self.sol.solve(("and", ("or", 3.0)))

    def test_deeply_nested_formula_does_not_recurse_error(self):
        # Validation and evaluation are iterative: a 5000-deep chain works.
        node = 0
        for _ in range(5000):
            node = ("not", node)
        self.assertTrue(self.sol.solve(node))  # even number of negations
        node = 0
        for _ in range(5001):
            node = ("and", node)
        self.assertTrue(self.sol.solve(node))
        bad = 0
        for _ in range(2000):
            bad = ("and", bad)
        bad = ("and", bad, 7)
        with self.assertRaises(ValidationError) as ctx:
            self.sol.solve(bad)
        self.assertIn("atom index 7", str(ctx.exception))


# ---------------------------------------------------------------------------
# Random cross-check against the independent reference
# ---------------------------------------------------------------------------

class TestBooleanReferenceCrossCheck(unittest.TestCase):
    def test_random_model_sets_match_reference(self):
        for seed in range(60):
            rng = random.Random(1000 + seed)
            sol, terms, atoms, formula = make_random_problem(
                rng, n_atoms=rng.randint(1, MAX_BOOLEAN_ATOMS))
            expected = set(ref_models(terms, atoms, formula))
            got = set(sol.all_models(formula))
            self.assertEqual(got, expected, f"seed={seed}")

    def test_random_first_answer_matches_reference(self):
        for seed in range(60):
            rng = random.Random(2000 + seed)
            sol, terms, atoms, formula = make_random_problem(
                rng, n_atoms=rng.randint(1, 5))
            expected = ref_models(terms, atoms, formula)
            result = sol.solve(formula)
            if expected:
                self.assertTrue(result.satisfiable, f"seed={seed}")
                self.assertIn(result.assignment, expected, f"seed={seed}")
                # First model is the lowest-mask one.
                self.assertEqual(result.assignment, expected[0],
                                 f"seed={seed}")
            else:
                self.assertFalse(result.satisfiable, f"seed={seed}")


if __name__ == "__main__":
    unittest.main()
