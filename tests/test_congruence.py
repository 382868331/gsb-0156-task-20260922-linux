"""Tests for congruence_closure.

The reference closure used for cross-checking is implemented independently
here (brute-force all-pairs fixed point) and never calls the module under
test to obtain expected values.
"""

import os
import random
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from congruence_closure import (  # noqa: E402
    ArityError,
    CongruenceClosure,
    ContradictionError,
    NodeLimitError,
    NotEqualError,
    ProofError,
    UnknownNodeError,
    ValidationError,
    verify_contradiction,
    verify_proof,
)


# ---------------------------------------------------------------------------
# Independent reference: enumerate the equivalence-relation closure by
# brute-force all-pairs fixed point (acceptable for small instances only).
# ---------------------------------------------------------------------------

def reference_closure(terms, equalities):
    """Return a find() closure for the equivalence relation induced by
    `equalities` plus congruence, computed by naive all-pairs iteration."""
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
                if fi != fj or find(i) == find(j):
                    continue
                if all(find(x) == find(y) for x, y in zip(ai, aj)):
                    union(i, j)
                    changed = True
    return find


def build_random_instance(rng, n_consts=3, n_terms=9, n_eqs=4):
    """Deterministically (via rng) build a small random DAG + equalities.

    Returns (cc, terms, equalities) where terms mirrors cc's table."""
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
    equalities = []
    for _ in range(n_eqs):
        a = rng.randrange(len(terms))
        b = rng.randrange(len(terms))
        if a != b:
            cc.assert_equal(a, b)
            equalities.append((a, b))
    return cc, terms, equalities


class TestBasicClosure(unittest.TestCase):
    def test_hashcons_sharing(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        f1 = cc.add_term("f", [a])
        f2 = cc.add_term("f", [a])
        self.assertEqual(f1, f2)
        self.assertEqual(cc.node_count, 2)

    def test_input_equality_and_transitivity(self):
        cc = CongruenceClosure()
        a, b, c = (cc.add_term(n) for n in "abc")
        cc.assert_equal(a, b)
        cc.assert_equal(b, c)
        self.assertTrue(cc.are_equal(a, c))
        self.assertEqual(cc.input_equalities, ((a, b), (b, c)))

    def test_multilayer_parent_propagation(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        gfa = cc.add_term("g", [fa])
        gfb = cc.add_term("g", [fb])
        hfa = cc.add_term("h", [gfa])
        hfb = cc.add_term("h", [gfb])
        cc.assert_equal(a, b)
        self.assertTrue(cc.are_equal(fa, fb))
        self.assertTrue(cc.are_equal(gfa, gfb))
        self.assertTrue(cc.are_equal(hfa, hfb))
        proof = cc.explain(hfa, hfb)
        self.assertTrue(verify_proof(proof, hfa, hfb,
                                     cc.input_equalities, cc.terms))

    def test_no_reverse_inference(self):
        # f(a) = f(b) must NOT imply a = b (congruence is one-directional).
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.assert_equal(fa, fb)
        self.assertFalse(cc.are_equal(a, b))
        with self.assertRaises(NotEqualError):
            cc.explain(a, b)

    def test_add_term_triggers_congruence(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        cc.assert_equal(a, b)
        fb = cc.add_term("f", [b])  # signature matches f(a): auto-merge
        self.assertNotEqual(fa, fb)
        self.assertTrue(cc.are_equal(fa, fb))

    def test_distinct_recorded_and_checked(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        c = cc.add_term("c")
        cc.assert_distinct(a, b)
        cc.assert_equal(a, c)
        with self.assertRaises(ContradictionError):
            cc.assert_equal(c, b)
        # Rolled back: c and b still distinct, a == c kept.
        self.assertFalse(cc.are_equal(c, b))
        self.assertTrue(cc.are_equal(a, c))

    def test_explain_not_equal_raises(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        with self.assertRaises(NotEqualError):
            cc.explain(a, b)


class TestContradictionProofs(unittest.TestCase):
    def test_conflict_proof_verifies(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        x = cc.add_term("x")
        y = cc.add_term("y")
        cc.assert_equal(x, fa)
        cc.assert_equal(y, fb)
        cc.assert_distinct(x, y)
        with self.assertRaises(ContradictionError) as ctx:
            cc.assert_equal(a, b)
        err = ctx.exception
        self.assertTrue(
            verify_contradiction(err.proof, err.inputs, err.distincts,
                                 err.terms))
        # The contradiction is derived through one congruence step.
        _, eq_proof, pair = err.proof
        self.assertEqual(set(pair), {x, y})
        kinds = [e[0] for e in eq_proof]
        self.assertIn("cong", kinds)
        self.assertIn("input", kinds)

    def test_distinct_of_equal_terms_fails_immediately(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        cc.assert_equal(a, b)
        with self.assertRaises(ContradictionError) as ctx:
            cc.assert_distinct(a, b)
        err = ctx.exception
        self.assertTrue(
            verify_contradiction(err.proof, err.inputs, err.distincts,
                                 err.terms))
        self.assertEqual(cc.distinct_assertions, ())

    def test_failed_assert_equal_is_atomic(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.assert_distinct(fa, fb)
        before_inputs = cc.input_equalities
        with self.assertRaises(ContradictionError):
            cc.assert_equal(a, b)  # would merge f(a), f(b) via congruence
        self.assertFalse(cc.are_equal(a, b))
        self.assertFalse(cc.are_equal(fa, fb))
        self.assertEqual(cc.input_equalities, before_inputs)


class TestBatch(unittest.TestCase):
    def test_batch_success(self):
        cc = CongruenceClosure()
        a, b, c, d = (cc.add_term(n) for n in "abcd")
        cc.apply_batch([("=", a, b), ("=", c, d), ("!=", a, c)])
        self.assertTrue(cc.are_equal(a, b))
        self.assertTrue(cc.are_equal(c, d))
        self.assertFalse(cc.are_equal(a, c))

    def test_batch_conflict_rolls_back_everything(self):
        cc = CongruenceClosure()
        a, b, c, d = (cc.add_term(n) for n in "abcd")
        cc.assert_distinct(c, d)
        before_inputs = cc.input_equalities
        before_distincts = cc.distinct_assertions
        with self.assertRaises(ContradictionError) as ctx:
            cc.apply_batch([("=", a, b), ("=", b, c), ("=", a, d)])
        err = ctx.exception
        self.assertTrue(
            verify_contradiction(err.proof, err.inputs, err.distincts,
                                 err.terms))
        # Nothing from the batch survived.
        self.assertFalse(cc.are_equal(a, b))
        self.assertFalse(cc.are_equal(b, c))
        self.assertFalse(cc.are_equal(a, d))
        self.assertEqual(cc.input_equalities, before_inputs)
        self.assertEqual(cc.distinct_assertions, before_distincts)

    def test_batch_conflict_via_congruence(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.assert_distinct(fa, fb)
        with self.assertRaises(ContradictionError):
            cc.apply_batch([("=", a, b)])
        self.assertFalse(cc.are_equal(a, b))

    def test_batch_validation_errors_locate_op(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        with self.assertRaises(ValidationError) as ctx:
            cc.apply_batch([("=", a, a), ("~", a, a)])
        self.assertIn("op 1", str(ctx.exception))
        with self.assertRaises(ValidationError) as ctx:
            cc.apply_batch([("=", a, 99)])
        self.assertIn("op 0", str(ctx.exception))


class TestExplainStability(unittest.TestCase):
    def test_explain_is_deterministic_and_stable(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.assert_equal(a, b)
        p1 = cc.explain(fa, fb)
        p2 = cc.explain(fa, fb)
        self.assertEqual(p1, p2)  # same state -> identical proof
        # Unrelated later assertions must not invalidate the proof.
        c = cc.add_term("c")
        d = cc.add_term("d")
        cc.assert_equal(c, d)
        self.assertTrue(verify_proof(p1, fa, fb, cc.input_equalities,
                                     cc.terms))
        p3 = cc.explain(fa, fb)
        self.assertTrue(verify_proof(p3, fa, fb, cc.input_equalities,
                                     cc.terms))

    def test_explain_chain_through_multiple_inputs(self):
        cc = CongruenceClosure()
        ids = [cc.add_term(f"c{i}") for i in range(5)]
        for i in range(4):
            cc.assert_equal(ids[i], ids[i + 1])
        proof = cc.explain(ids[0], ids[4])
        self.assertEqual(len(proof), 4)
        self.assertTrue(all(e[0] == "input" for e in proof))
        self.assertTrue(verify_proof(proof, ids[0], ids[4],
                                     cc.input_equalities, cc.terms))


class TestReferenceCrossCheck(unittest.TestCase):
    def test_random_instances_match_reference(self):
        for seed in range(30):
            rng = random.Random(seed)
            cc, terms, equalities = build_random_instance(rng)
            find = reference_closure(terms, equalities)
            n = len(terms)
            for i in range(n):
                for j in range(n):
                    self.assertEqual(
                        cc.are_equal(i, j), find(i) == find(j),
                        f"seed={seed} pair=({i},{j})")

    def test_random_proofs_verify(self):
        for seed in range(30, 45):
            rng = random.Random(seed)
            cc, terms, equalities = build_random_instance(rng)
            find = reference_closure(terms, equalities)
            n = len(terms)
            for i in range(n):
                for j in range(i + 1, n):
                    if find(i) == find(j):
                        proof = cc.explain(i, j)
                        self.assertTrue(
                            verify_proof(proof, i, j, cc.input_equalities,
                                         cc.terms),
                            f"seed={seed} pair=({i},{j})")
                    else:
                        with self.assertRaises(NotEqualError):
                            cc.explain(i, j)


class TestProofVerifierNegative(unittest.TestCase):
    def setUp(self):
        cc = CongruenceClosure()
        self.a = cc.add_term("a")
        self.b = cc.add_term("b")
        self.fa = cc.add_term("f", [self.a])
        self.fb = cc.add_term("f", [self.b])
        cc.assert_equal(self.a, self.b)
        self.cc = cc
        self.proof = cc.explain(self.fa, self.fb)

    def test_tampered_endpoint_rejected(self):
        with self.assertRaises(ProofError):
            verify_proof(self.proof, self.fa, self.a,
                         self.cc.input_equalities, self.cc.terms)

    def test_unknown_input_rejected(self):
        forged = (("input", self.a, self.b),)
        with self.assertRaises(ProofError):
            verify_proof(forged, self.a, self.b, (), self.cc.terms)

    def test_bad_congruence_symbol_rejected(self):
        g = self.cc.add_term("g", [self.a])
        forged = (("cong", self.fa, g, ((),)),)
        with self.assertRaises(ProofError):
            verify_proof(forged, self.fa, g,
                         self.cc.input_equalities, self.cc.terms)

    def test_valid_proof_accepted(self):
        self.assertTrue(
            verify_proof(self.proof, self.fa, self.fb,
                         self.cc.input_equalities, self.cc.terms))

    def test_contradiction_requires_distinct_membership(self):
        proof = ("contradiction", (("input", self.a, self.b),),
                 (self.a, self.b))
        with self.assertRaises(ProofError):
            verify_contradiction(proof, self.cc.input_equalities, (),
                                 self.cc.terms)


class TestValidation(unittest.TestCase):
    def setUp(self):
        self.cc = CongruenceClosure()
        self.a = self.cc.add_term("a")

    def test_bool_rejected_as_node_id(self):
        with self.assertRaises(ValidationError):
            self.cc.add_term("f", [True])
        with self.assertRaises(ValidationError):
            self.cc.assert_equal(self.a, False)

    def test_float_and_nan_rejected_as_node_id(self):
        for bad in (0.0, float("nan"), float("inf"), float("-inf")):
            with self.assertRaises(ValidationError):
                self.cc.assert_equal(self.a, bad)

    def test_unknown_node_rejected(self):
        with self.assertRaises(UnknownNodeError):
            self.cc.assert_equal(self.a, 7)
        with self.assertRaises(UnknownNodeError):
            self.cc.explain(-1, self.a)

    def test_bad_function_symbol(self):
        for bad in ("", None, 3, b"f"):
            with self.assertRaises(ValidationError):
                self.cc.add_term(bad)

    def test_arity_fixed_at_first_use(self):
        self.cc.add_term("f", [self.a])
        with self.assertRaises(ArityError):
            self.cc.add_term("f", [self.a, self.a])
        with self.assertRaises(ArityError):
            self.cc.add_term("f")

    def test_node_limit(self):
        cc = CongruenceClosure(max_nodes=2)
        cc.add_term("a")
        cc.add_term("b")
        with self.assertRaises(NodeLimitError):
            cc.add_term("c")

    def test_max_nodes_validation(self):
        with self.assertRaises(ValidationError):
            CongruenceClosure(max_nodes=True)
        with self.assertRaises(ValidationError):
            CongruenceClosure(max_nodes=-1)
        with self.assertRaises(ValidationError):
            CongruenceClosure(max_nodes=1.5)


class TestDeepTerms(unittest.TestCase):
    def test_deep_chain_explain(self):
        # Depth beyond the default recursion limit: explain must cope.
        depth = 1500
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        ta, tb = a, b
        for _ in range(depth):
            ta = cc.add_term("f", [ta])
            tb = cc.add_term("f", [tb])
        cc.assert_equal(a, b)
        self.assertTrue(cc.are_equal(ta, tb))
        proof = cc.explain(ta, tb)
        self.assertTrue(verify_proof(proof, ta, tb, cc.input_equalities,
                                     cc.terms))


if __name__ == "__main__":
    unittest.main()
