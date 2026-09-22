"""Tests for the congruence_closure package.

The reference implementation below computes the congruence closure by naive
repeated enumeration of all term pairs.  It never imports or calls the
engine under test; expected values come from it, not from the core.
"""

import random
import unittest

from congruence_closure import (
    BudgetExhaustedError,
    CongruenceClosure,
    ConflictError,
    InvalidInputError,
    InvalidProofError,
    LimitExceededError,
    NotEqualError,
    verify_proof,
)


# ---------------------------------------------------------------------------
# Independent reference: enumerate the equivalence closure by fixpoint.
# ---------------------------------------------------------------------------

class ReferenceClosure:
    """Naive O(n^2)-per-round congruence closure over a flat term table."""

    def __init__(self, terms):
        # terms: list of (symbol, tuple-of-arg-indices)
        self.terms = terms
        self.parent = list(range(len(terms)))

    def find(self, x):
        while self.parent[x] != x:
            x = self.parent[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.parent[ra] = rb

    def close(self, equalities):
        for a, b in equalities:
            self.union(a, b)
        changed = True
        while changed:
            changed = False
            for i in range(len(self.terms)):
                si, ai = self.terms[i]
                for j in range(i + 1, len(self.terms)):
                    sj, aj = self.terms[j]
                    if si != sj or len(ai) != len(aj):
                        continue
                    if self.find(i) == self.find(j):
                        continue
                    if all(self.find(x) == self.find(y)
                           for x, y in zip(ai, aj)):
                        self.union(i, j)
                        changed = True

    def equal(self, a, b):
        return self.find(a) == self.find(b)


def build_random_instance(rng, n_terms, n_eq):
    """Deterministically build (engine, terms, ids, equalities).

    ``terms`` mirrors the engine's DAG so the reference closure can run on
    exactly the same input without touching the engine.
    """
    consts = ["c0", "c1", "c2", "c3", "c4"]
    funcs = [("f", 2), ("g", 1), ("h", 2), ("k", 3)]
    cc = CongruenceClosure()
    terms = []
    dedup = {}
    for i in range(n_terms):
        if i < 2 or rng.random() < 0.35 or not terms:
            sym, args = rng.choice(consts), ()
        else:
            sym, ar = rng.choice(funcs)
            args = tuple(rng.randrange(len(terms)) for _ in range(ar))
        key = (sym, args)
        if key in dedup:
            expected = dedup[key]
        else:
            expected = len(terms)
            dedup[key] = expected
            terms.append(key)
        tid = cc.add_term(sym, list(args))
        assert tid == expected, "hash-consing order mismatch"
    equalities = []
    for _ in range(n_eq):
        a = rng.randrange(len(terms))
        b = rng.randrange(len(terms))
        if a != b:
            equalities.append((a, b))
    return cc, terms, equalities


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

class TestBasicCongruence(unittest.TestCase):
    def test_constants_and_hash_consing(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        self.assertNotEqual(a, b)
        self.assertEqual(cc.add_term("a"), a)  # hash-consed
        f1 = cc.add_term("f", [a, b])
        f2 = cc.add_term("f", [a, b])
        self.assertEqual(f1, f2)
        self.assertEqual(cc.term_count, 3)
        self.assertEqual(cc.term(f1), ("f", (a, b)))

    def test_congruence_one_level(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        self.assertFalse(cc.are_equal(fa, fb))
        self.assertTrue(cc.assert_equal(a, b))
        self.assertTrue(cc.are_equal(fa, fb))
        self.assertFalse(cc.assert_equal(a, b))  # already equal: no-op

    def test_multi_level_parent_propagation(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        depth = 300
        ta, tb = [a], [b]
        for _ in range(depth):
            ta.append(cc.add_term("g", [ta[-1]]))
            tb.append(cc.add_term("g", [tb[-1]]))
        cc.assert_equal(a, b)
        for k in (1, 2, 7, 100, depth):
            self.assertTrue(cc.are_equal(ta[k], tb[k]),
                            f"g^{k}(a) should equal g^{k}(b)")
        # proof of the deepest equality verifies independently
        lhs, rhs = verify_proof(cc.explain(ta[depth], tb[depth]),
                                cc.input_equalities())
        self.assertEqual(lhs, cc.term_structure(ta[depth]))
        self.assertEqual(rhs, cc.term_structure(tb[depth]))

    def test_no_reverse_inference(self):
        # f(a) = f(b) must NOT imply a = b.
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.assert_equal(fa, fb)
        self.assertFalse(cc.are_equal(a, b))
        # deeper: f(g(a)) = f(g(b)) implies neither g(a)=g(b) nor a=b
        ga = cc.add_term("g", [a])
        gb = cc.add_term("g", [b])
        fga = cc.add_term("h", [ga])
        fgb = cc.add_term("h", [gb])
        cc.assert_equal(fga, fgb)
        self.assertFalse(cc.are_equal(ga, gb))
        self.assertFalse(cc.are_equal(a, b))

    def test_distinct_immediate_conflict(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        cc.assert_equal(a, b)
        with self.assertRaises(ConflictError) as cm:
            cc.assert_distinct(a, b)
        lhs, rhs = verify_proof(cm.exception.proof,
                                cm.exception.input_equalities)
        self.assertEqual({lhs, rhs},
                         {cc.term_structure(a), cc.term_structure(b)})

    def test_distinct_delayed_conflict_and_proof(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        x = cc.add_term("x")
        cc.assert_distinct(a, b)
        cc.assert_equal(a, x)
        with self.assertRaises(ConflictError) as cm:
            cc.assert_equal(x, b)
        self.assertEqual(set(cm.exception.pair), {a, b})
        lhs, rhs = verify_proof(cm.exception.proof,
                                cm.exception.input_equalities)
        self.assertEqual({lhs, rhs},
                         {cc.term_structure(a), cc.term_structure(b)})
        # failed assert_equal rolled back: x and b are unrelated again
        self.assertFalse(cc.are_equal(x, b))
        self.assertTrue(cc.are_equal(a, x))  # earlier assertion intact


class TestExplain(unittest.TestCase):
    def _engine(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        c = cc.add_term("c")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        ffa = cc.add_term("f", [fa])
        ffb = cc.add_term("f", [fb])
        cc.assert_equal(a, b)
        cc.assert_equal(b, c)
        return cc, a, b, c, fa, fb, ffa, ffb

    def test_explain_verifies_and_is_stable(self):
        cc, a, b, c, fa, fb, ffa, ffb = self._engine()
        p1 = cc.explain(ffa, ffb)
        p2 = cc.explain(ffa, ffb)
        self.assertEqual(p1, p2)  # stability: identical tree on repeat
        lhs, rhs = verify_proof(p1, cc.input_equalities())
        self.assertEqual(lhs, cc.term_structure(ffa))
        self.assertEqual(rhs, cc.term_structure(ffb))

    def test_explain_transitive_chain(self):
        cc, a, b, c, *_ = self._engine()
        proof = cc.explain(a, c)
        lhs, rhs = verify_proof(proof, cc.input_equalities())
        self.assertEqual(lhs, cc.term_structure(a))
        self.assertEqual(rhs, cc.term_structure(c))

    def test_explain_self_is_refl(self):
        cc, a, *_ = self._engine()
        proof = cc.explain(a, a)
        lhs, rhs = verify_proof(proof, cc.input_equalities())
        self.assertEqual(lhs, rhs)
        self.assertEqual(lhs, cc.term_structure(a))

    def test_explain_not_equal_raises(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        with self.assertRaises(NotEqualError):
            cc.explain(a, b)

    def test_tampered_proof_rejected(self):
        cc, a, b, c, fa, fb, ffa, ffb = self._engine()
        proof = cc.explain(ffa, ffb)
        # wrong input index
        with self.assertRaises(InvalidProofError):
            verify_proof(("input", 99), cc.input_equalities())
        # transitivity midpoint mismatch
        with self.assertRaises(InvalidProofError):
            verify_proof(("trans", ("input", 0), ("input", 0)),
                         cc.input_equalities())
        # unknown tag / malformed nodes
        with self.assertRaises(InvalidProofError):
            verify_proof(("bogus",), cc.input_equalities())
        with self.assertRaises(InvalidProofError):
            verify_proof(("cong", "f", [("refl", ("a", ()))], "extra"),
                         cc.input_equalities())
        # a valid proof of something else is not a proof of ffa == ffb
        other = cc.explain(a, b)
        lhs, rhs = verify_proof(other, cc.input_equalities())
        self.assertNotEqual((lhs, rhs),
                            (cc.term_structure(ffa), cc.term_structure(ffb)))
        self.assertIsInstance(proof, tuple)


class TestBatchAndRollback(unittest.TestCase):
    def _snapshot(self, cc):
        n = cc.term_count
        matrix = tuple(
            tuple(cc.are_equal(i, j) for j in range(n)) for i in range(n))
        return matrix, cc.term_count, cc.class_count, cc.input_equalities()

    def test_batch_conflict_rolls_back_everything(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        c = cc.add_term("c")
        d = cc.add_term("d")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.assert_equal(a, b)  # pre-existing state
        cc.assert_distinct(c, d)
        before = self._snapshot(cc)
        with self.assertRaises(ConflictError) as cm:
            cc.assert_batch(equalities=[(fa, fb), (c, fa), (fa, d)],
                            distincts=[])
        self.assertEqual(self._snapshot(cc), before)
        # conflict proof still verifies standalone
        lhs, rhs = verify_proof(cm.exception.proof,
                                cm.exception.input_equalities)
        self.assertEqual({lhs, rhs},
                         {cc.term_structure(c), cc.term_structure(d)})

    def test_batch_distincts_param_conflict_rolls_back_equalities(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        c = cc.add_term("c")
        before = self._snapshot(cc)
        with self.assertRaises(ConflictError):
            cc.assert_batch(equalities=[(a, b), (b, c)],
                            distincts=[(a, c)])
        self.assertEqual(self._snapshot(cc), before)

    def test_batch_invalid_element_rolls_back(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        c = cc.add_term("c")
        before = self._snapshot(cc)
        with self.assertRaises(InvalidInputError):
            cc.assert_batch(equalities=[(a, b), (b, "not-an-id")])
        self.assertEqual(self._snapshot(cc), before)
        self.assertFalse(cc.are_equal(a, b))
        self.assertFalse(cc.are_equal(b, c))

    def test_successful_batch_applies_all(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        c = cc.add_term("c")
        d = cc.add_term("d")
        cc.assert_batch(equalities=[(a, b), (c, d)], distincts=[(a, c)])
        self.assertTrue(cc.are_equal(a, b))
        self.assertTrue(cc.are_equal(c, d))
        self.assertFalse(cc.are_equal(a, c))
        with self.assertRaises(ConflictError):
            cc.assert_equal(b, d)
        self.assertFalse(cc.are_equal(b, d))  # rolled back


class TestInputValidation(unittest.TestCase):
    def setUp(self):
        self.cc = CongruenceClosure()
        self.a = self.cc.add_term("a")
        self.b = self.cc.add_term("b")

    def test_term_id_validation(self):
        for bad in (True, False, 1.5, float("nan"), float("inf"),
                    float("-inf"), "0", None, -1, 10**9):
            with self.assertRaises(InvalidInputError, msg=repr(bad)):
                self.cc.are_equal(bad, self.a)
            with self.assertRaises(InvalidInputError, msg=repr(bad)):
                self.cc.assert_equal(self.a, bad)

    def test_symbol_validation(self):
        for bad in ("", 0, 1.5, float("nan"), None, True, b"x"):
            with self.assertRaises(InvalidInputError, msg=repr(bad)):
                self.cc.add_term(bad)

    def test_args_validation(self):
        with self.assertRaises(InvalidInputError):
            self.cc.add_term("f", "ab")
        with self.assertRaises(InvalidInputError):
            self.cc.add_term("f", [self.a, None])
        with self.assertRaises(InvalidInputError):
            self.cc.add_term("f", [self.a, True])

    def test_arity_is_fixed_per_symbol(self):
        self.cc.add_term("f", [self.a])
        with self.assertRaises(InvalidInputError):
            self.cc.add_term("f", [self.a, self.b])
        with self.assertRaises(InvalidInputError):
            self.cc.add_term("f")  # was arity 1

    def test_constructor_validation(self):
        for bad in (True, 0, -3, 2.5, float("nan"), float("inf"), "5"):
            with self.assertRaises(InvalidInputError, msg=repr(bad)):
                CongruenceClosure(max_terms=bad)
        for bad in (True, -1, 0.5, float("inf"), None):
            with self.assertRaises(InvalidInputError, msg=repr(bad)):
                CongruenceClosure(work_budget=bad)

    def test_term_limit(self):
        cc = CongruenceClosure(max_terms=3)
        cc.add_term("a")
        cc.add_term("b")
        cc.add_term("c")
        with self.assertRaises(LimitExceededError):
            cc.add_term("d")
        cc.add_term("a")  # hash-consed re-add does not consume budget

    def test_budget_exhaustion_is_not_conflict(self):
        # Merging a,b must propagate to f(a),f(b): needs more than 2 steps.
        cc = CongruenceClosure(work_budget=2)
        a = cc.add_term("a")
        b = cc.add_term("b")
        cc.add_term("f", [a])
        cc.add_term("f", [b])
        with self.assertRaises(BudgetExhaustedError):
            cc.assert_equal(a, b)
        # rolled back, and it is a different condition than ConflictError
        self.assertFalse(cc.are_equal(a, b))
        self.assertFalse(issubclass(BudgetExhaustedError, ConflictError))
        # with enough budget the same call succeeds
        cc2 = CongruenceClosure()
        a2 = cc2.add_term("a")
        b2 = cc2.add_term("b")
        fa2 = cc2.add_term("f", [a2])
        fb2 = cc2.add_term("f", [b2])
        cc2.assert_equal(a2, b2)
        self.assertTrue(cc2.are_equal(fa2, fb2))


class TestAgainstReference(unittest.TestCase):
    def test_random_instances_match_reference(self):
        for seed in range(25):
            rng = random.Random(1000 + seed)
            cc, terms, equalities = build_random_instance(
                rng, n_terms=40, n_eq=15)
            for a, b in equalities:
                cc.assert_equal(a, b)
            ref = ReferenceClosure(terms)
            ref.close(equalities)
            n = len(terms)
            for i in range(n):
                for j in range(n):
                    self.assertEqual(
                        cc.are_equal(i, j), ref.equal(i, j),
                        f"seed={seed} pair=({i},{j})")

    def test_random_distinct_matches_reference(self):
        rng = random.Random(77)
        cc, terms, equalities = build_random_instance(
            rng, n_terms=30, n_eq=10)
        for a, b in equalities:
            cc.assert_equal(a, b)
        ref = ReferenceClosure(terms)
        ref.close(equalities)
        for _ in range(60):
            a = rng.randrange(len(terms))
            b = rng.randrange(len(terms))
            if ref.equal(a, b):
                with self.assertRaises(ConflictError):
                    cc.assert_distinct(a, b)
            else:
                cc.assert_distinct(a, b)
                # still consistent afterwards
                self.assertFalse(cc.are_equal(a, b))

    def test_reference_itself_detects_no_reverse(self):
        # sanity check of the reference: f(a)=f(b) alone keeps a,b apart
        terms = [("a", ()), ("b", ()), ("f", (0,)), ("f", (1,))]
        ref = ReferenceClosure(terms)
        ref.close([(2, 3)])
        self.assertFalse(ref.equal(0, 1))
        self.assertTrue(ref.equal(2, 3))


if __name__ == "__main__":
    unittest.main()
