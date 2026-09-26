"""Tests for injective function symbols (backward argument propagation).

The reference closure used for cross-checking is implemented independently
here (brute-force all-pairs fixed point over equality + congruence +
injectivity) and never calls the module under test to obtain expected
values.
"""

import os
import random
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from congruence_closure import (  # noqa: E402
    CongruenceClosure,
    ContradictionError,
    NotEqualError,
    ProofError,
    ValidationError,
    verify_contradiction,
    verify_proof,
)


# ---------------------------------------------------------------------------
# Independent reference: brute-force fixed point over the equivalence
# relation induced by input equalities, congruence, and injectivity.
# ---------------------------------------------------------------------------

def reference_closure(terms, equalities, injective):
    """Naive all-pairs fixed point closure (small instances only)."""
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
                if fi != fj:
                    continue
                if find(i) != find(j) and all(
                        find(x) == find(y) for x, y in zip(ai, aj)):
                    union(i, j)  # congruence
                    changed = True
                if fi in injective and find(i) == find(j):
                    for x, y in zip(ai, aj):
                        if find(x) != find(y):
                            union(x, y)  # injectivity (backward)
                            changed = True
    return find


def build_random_instance(rng, n_consts=3, n_terms=8, n_eqs=3,
                          injective_funcs=("f",)):
    """Deterministically build a small random DAG + equalities, with the
    given function symbols declared injective."""
    cc = CongruenceClosure()
    terms = []
    consts = []
    for i in range(n_consts):
        nid = cc.add_term(f"c{i}")
        consts.append(nid)
        terms.append((f"c{i}", ()))
    funcs = [("f", 1), ("g", 2), ("h", 1)]
    for _ in range(n_terms):
        f, ar = rng.choice(funcs)
        args = tuple(rng.randrange(len(terms)) for _ in range(ar))
        nid = cc.add_term(f, args)
        if nid == len(terms):
            terms.append((f, args))
    for func in injective_funcs:
        cc.declare_injective(func)
    equalities = []
    for _ in range(n_eqs):
        a = rng.randrange(len(terms))
        b = rng.randrange(len(terms))
        if a != b:
            cc.assert_equal(a, b)
            equalities.append((a, b))
    return cc, terms, equalities


class TestInjectiveBasics(unittest.TestCase):
    def test_unary_backward_propagation(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.declare_injective("f")
        cc.assert_equal(fa, fb)
        self.assertTrue(cc.are_equal(a, b))
        proof = cc.explain(a, b)
        self.assertEqual([e[0] for e in proof], ["inj"])
        self.assertTrue(verify_proof(proof, a, b, cc.input_equalities,
                                     cc.terms, cc.injective_functions))

    def test_undeclared_function_stays_one_directional(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.assert_equal(fa, fb)
        self.assertFalse(cc.are_equal(a, b))
        with self.assertRaises(NotEqualError):
            cc.explain(a, b)

    def test_nested_injective_chain(self):
        # f(f(a)) = f(f(b)) with f injective => f(a) = f(b) => a = b.
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        ffa = cc.add_term("f", [fa])
        ffb = cc.add_term("f", [fb])
        cc.declare_injective("f")
        cc.assert_equal(ffa, ffb)
        self.assertTrue(cc.are_equal(fa, fb))
        self.assertTrue(cc.are_equal(a, b))
        proof = cc.explain(a, b)
        # One injective step whose premise is itself an injective step.
        self.assertEqual([e[0] for e in proof], ["inj"])
        self.assertEqual(proof[0][4][0][0], "inj")
        self.assertTrue(verify_proof(proof, a, b, cc.input_equalities,
                                     cc.terms, cc.injective_functions))

    def test_binary_arguments_positionwise(self):
        # g injective binary: g(x, y) = g(u, v) => x = u and y = v.
        cc = CongruenceClosure()
        x, y, u, v = (cc.add_term(n) for n in "xyuv")
        g1 = cc.add_term("g", [x, y])
        g2 = cc.add_term("g", [u, v])
        cc.declare_injective("g")
        cc.assert_equal(g1, g2)
        self.assertTrue(cc.are_equal(x, u))
        self.assertTrue(cc.are_equal(y, v))
        self.assertFalse(cc.are_equal(x, v))
        self.assertTrue(verify_proof(cc.explain(y, v), y, v,
                                     cc.input_equalities, cc.terms,
                                     cc.injective_functions))

    def test_binary_arguments_swapped(self):
        # g injective: g(x, y) = g(y, x) forces x = y via either position.
        cc = CongruenceClosure()
        x = cc.add_term("x")
        y = cc.add_term("y")
        g1 = cc.add_term("g", [x, y])
        g2 = cc.add_term("g", [y, x])
        cc.declare_injective("g")
        cc.assert_equal(g1, g2)
        self.assertTrue(cc.are_equal(x, y))
        self.assertTrue(verify_proof(cc.explain(x, y), x, y,
                                     cc.input_equalities, cc.terms,
                                     cc.injective_functions))

    def test_backward_then_forward_chain(self):
        # Injective backward step feeds forward congruence:
        # h(f(a)) = h(f(b)), h injective => f(a) = f(b) (backward);
        # then g(f(a)) = g(f(b)) by forward congruence.
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        hfa = cc.add_term("h", [fa])
        hfb = cc.add_term("h", [fb])
        gfa = cc.add_term("g", [fa])
        gfb = cc.add_term("g", [fb])
        cc.declare_injective("h")
        cc.assert_equal(hfa, hfb)
        self.assertTrue(cc.are_equal(fa, fb))
        self.assertTrue(cc.are_equal(gfa, gfb))
        self.assertFalse(cc.are_equal(a, b))  # f not injective
        proof = cc.explain(gfa, gfb)
        self.assertTrue(verify_proof(proof, gfa, gfb, cc.input_equalities,
                                     cc.terms, cc.injective_functions))

    def test_forward_then_backward_chain(self):
        # a = b (input) => f(a) = f(b) (congruence); f injective and
        # f(a) = f(c) asserted => a = c via backward, so b = c too.
        cc = CongruenceClosure()
        a, b, c = (cc.add_term(n) for n in "abc")
        fa = cc.add_term("f", [a])
        fc = cc.add_term("f", [c])
        cc.declare_injective("f")
        cc.assert_equal(a, b)
        cc.assert_equal(fa, fc)
        self.assertTrue(cc.are_equal(b, c))
        self.assertTrue(verify_proof(cc.explain(b, c), b, c,
                                     cc.input_equalities, cc.terms,
                                     cc.injective_functions))

    def test_declare_after_terms_exist_is_retroactive(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.assert_equal(fa, fb)
        self.assertFalse(cc.are_equal(a, b))
        cc.declare_injective("f")  # retroactively derives a = b
        self.assertTrue(cc.are_equal(a, b))
        self.assertTrue(verify_proof(cc.explain(a, b), a, b,
                                     cc.input_equalities, cc.terms,
                                     cc.injective_functions))

    def test_redeclare_is_noop_and_idempotent(self):
        cc = CongruenceClosure()
        cc.declare_injective("f")
        cc.declare_injective("f")
        self.assertEqual(cc.injective_functions, ("f",))

    def test_declare_injective_validation(self):
        cc = CongruenceClosure()
        for bad in ("", None, 3, b"f"):
            with self.assertRaises(ValidationError):
                cc.declare_injective(bad)


class TestInjectiveConflicts(unittest.TestCase):
    def test_conflict_with_distinct_and_proof(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.declare_injective("f")
        cc.assert_distinct(a, b)
        with self.assertRaises(ContradictionError) as ctx:
            cc.assert_equal(fa, fb)
        err = ctx.exception
        self.assertTrue(
            verify_contradiction(err.proof, err.inputs, err.distincts,
                                 err.terms, err.injective))
        _, eq_proof, pair = err.proof
        self.assertEqual(set(pair), {a, b})
        self.assertIn("inj", [e[0] for e in eq_proof])
        self.assertIn("f", err.injective)
        # Rolled back: nothing derived.
        self.assertFalse(cc.are_equal(fa, fb))
        self.assertFalse(cc.are_equal(a, b))

    def test_retroactive_declaration_conflict_rolls_back(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.assert_equal(fa, fb)
        cc.assert_distinct(a, b)
        with self.assertRaises(ContradictionError) as ctx:
            cc.declare_injective("f")
        err = ctx.exception
        self.assertTrue(
            verify_contradiction(err.proof, err.inputs, err.distincts,
                                 err.terms, err.injective))
        # Declaration rolled back: f is not injective anymore.
        self.assertEqual(cc.injective_functions, ())
        self.assertFalse(cc.are_equal(a, b))

    def test_batch_conflict_via_injectivity(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.declare_injective("f")
        cc.assert_distinct(a, b)
        before = cc.input_equalities
        with self.assertRaises(ContradictionError):
            cc.apply_batch([("=", fa, fb)])
        self.assertEqual(cc.input_equalities, before)
        self.assertFalse(cc.are_equal(fa, fb))


class TestInjectiveProofVerification(unittest.TestCase):
    def setUp(self):
        cc = CongruenceClosure()
        self.a = cc.add_term("a")
        self.b = cc.add_term("b")
        self.fa = cc.add_term("f", [self.a])
        self.fb = cc.add_term("f", [self.b])
        cc.declare_injective("f")
        cc.assert_equal(self.fa, self.fb)
        self.cc = cc
        self.proof = cc.explain(self.a, self.b)

    def test_inj_proof_rejected_without_injective_declaration(self):
        # The independent checker must not trust the core: without the
        # injective declaration the same proof is invalid.
        with self.assertRaises(ProofError):
            verify_proof(self.proof, self.a, self.b,
                         self.cc.input_equalities, self.cc.terms)

    def test_inj_proof_accepted_with_declaration(self):
        self.assertTrue(
            verify_proof(self.proof, self.a, self.b,
                         self.cc.input_equalities, self.cc.terms,
                         self.cc.injective_functions))

    def test_inj_step_for_undeclared_symbol_rejected(self):
        g = self.cc.add_term("g", [self.a])
        h = self.cc.add_term("g", [self.b])
        forged = (("inj", g, h, 0, (("input", self.fa, self.fb),)),)
        with self.assertRaises(ProofError):
            verify_proof(forged, self.a, self.b, self.cc.input_equalities,
                         self.cc.terms, ("f",))

    def test_inj_step_with_false_premise_rejected(self):
        # Premise subproof must genuinely derive t1 = t2.
        forged = (("inj", self.fa, self.fb, 0, ()),)
        with self.assertRaises(ProofError):
            verify_proof(forged, self.a, self.b, self.cc.input_equalities,
                         self.cc.terms, ("f",))

    def test_inj_step_bad_index_rejected(self):
        premise = (("input", self.fa, self.fb),)
        forged = (("inj", self.fa, self.fb, 5, premise),)
        with self.assertRaises(ProofError):
            verify_proof(forged, self.a, self.b, self.cc.input_equalities,
                         self.cc.terms, ("f",))


class TestInjectiveReferenceCrossCheck(unittest.TestCase):
    def test_random_instances_match_reference(self):
        for seed in range(40):
            rng = random.Random(1000 + seed)
            injective = rng.choice([("f",), ("g",), ("f", "g"), ()])
            cc, terms, equalities = build_random_instance(
                rng, injective_funcs=injective)
            find = reference_closure(terms, equalities, set(injective))
            n = len(terms)
            for i in range(n):
                for j in range(n):
                    self.assertEqual(
                        cc.are_equal(i, j), find(i) == find(j),
                        f"seed={seed} injective={injective} pair=({i},{j})")

    def test_random_proofs_verify(self):
        for seed in range(40, 55):
            rng = random.Random(1000 + seed)
            injective = rng.choice([("f",), ("g",), ("f", "g")])
            cc, terms, equalities = build_random_instance(
                rng, injective_funcs=injective)
            find = reference_closure(terms, equalities, set(injective))
            n = len(terms)
            for i in range(n):
                for j in range(i + 1, n):
                    if find(i) == find(j):
                        proof = cc.explain(i, j)
                        self.assertTrue(
                            verify_proof(proof, i, j, cc.input_equalities,
                                         cc.terms, cc.injective_functions),
                            f"seed={seed} pair=({i},{j})")
                    else:
                        with self.assertRaises(NotEqualError):
                            cc.explain(i, j)

    def test_random_satisfiability_matches_reference(self):
        # Satisfiability under distinct assertions: brute-force the
        # reference closure and compare with the core's accept/reject.
        for seed in range(25):
            rng = random.Random(2000 + seed)
            injective = rng.choice([("f",), ("g",), ("f", "g")])
            cc, terms, equalities = build_random_instance(
                rng, n_eqs=2, injective_funcs=injective)
            find = reference_closure(terms, equalities, set(injective))
            n = len(terms)
            for _ in range(4):
                x = rng.randrange(n)
                y = rng.randrange(n)
                if x == y:
                    continue
                ref_sat = find(x) != find(y)
                try:
                    cc.assert_distinct(x, y)
                    got_sat = True
                except ContradictionError as err:
                    got_sat = False
                    self.assertTrue(
                        verify_contradiction(
                            err.proof, err.inputs, err.distincts,
                            err.terms, err.injective))
                self.assertEqual(got_sat, ref_sat,
                                 f"seed={seed} pair=({x},{y})")
                if not got_sat:
                    break  # structure unchanged after failed assertion


if __name__ == "__main__":
    unittest.main()
