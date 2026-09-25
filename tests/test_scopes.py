"""Tests for push/pop scoped assumptions in congruence_closure.

The cross-check at the end replays the live assertions of every operation
prefix into a brand-new CongruenceClosure and compares all query results;
proof leaves are independently checked against the currently live
assertion levels.
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
    ScopeError,
    StaleNodeError,
    UnknownNodeError,
    verify_contradiction,
    verify_proof,
)


def _norm(a, b):
    return (a, b) if a <= b else (b, a)


def proof_input_leaves(proof):
    """Yield every (x, y) input-equality leaf used by an equality proof."""
    for edge in proof:
        if edge[0] == "input":
            yield (edge[1], edge[2])
        else:
            for sub in edge[3]:
                yield from proof_input_leaves(sub)


class TestScopeBasics(unittest.TestCase):
    def test_push_pop_restores_equality_classes(self):
        cc = CongruenceClosure()
        a, b, c = (cc.add_term(n) for n in "abc")
        cc.assert_equal(a, b)
        cc.push()
        cc.assert_equal(b, c)
        self.assertTrue(cc.are_equal(a, c))
        cc.pop()
        self.assertTrue(cc.are_equal(a, b))      # outer fact kept
        self.assertFalse(cc.are_equal(a, c))     # inner merge undone
        self.assertFalse(cc.are_equal(b, c))
        self.assertEqual(cc.input_equalities, ((a, b),))
        self.assertEqual(cc.scope_depth, 0)

    def test_multilevel_congruence_merges_inside_scope(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        gfa = cc.add_term("g", [fa])
        gfb = cc.add_term("g", [fb])
        hfa = cc.add_term("h", [gfa])
        hfb = cc.add_term("h", [gfb])
        cc.push()
        cc.assert_equal(a, b)
        # one input equality triggers a chain of congruence merges
        self.assertTrue(cc.are_equal(fa, fb))
        self.assertTrue(cc.are_equal(gfa, gfb))
        self.assertTrue(cc.are_equal(hfa, hfb))
        proof = cc.explain(hfa, hfb)
        self.assertTrue(
            verify_proof(proof, hfa, hfb, cc.input_equalities, cc.terms))
        cc.pop()
        for x, y in ((a, b), (fa, fb), (gfa, gfb), (hfa, hfb)):
            self.assertFalse(cc.are_equal(x, y))
        with self.assertRaises(NotEqualError):
            cc.explain(hfa, hfb)

    def test_nested_scopes_restore_parent_signatures(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        cc.push()
        cc.assert_equal(a, b)
        fb_inner = cc.add_term("f", [b])   # signature matches f(a): merged
        self.assertTrue(cc.are_equal(fa, fb_inner))
        cc.pop()
        # After the pop the signature table must be back to the outer
        # state: a fresh f(b) is a new node and NOT equal to f(a).
        fb = cc.add_term("f", [b])
        self.assertNotEqual(fb, fb_inner)
        self.assertFalse(cc.are_equal(fa, fb))
        # And the outer state can still evolve independently.
        cc.assert_equal(a, b)
        self.assertTrue(cc.are_equal(fa, fb))

    def test_pop_at_base_raises_and_keeps_state(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        cc.assert_equal(a, b)
        with self.assertRaises(ScopeError):
            cc.pop()
        with self.assertRaises(ScopeError):
            cc.pop()
        # base state untouched
        self.assertTrue(cc.are_equal(a, b))
        self.assertEqual(cc.input_equalities, ((a, b),))
        self.assertEqual(cc.scope_depth, 0)

    def test_context_manager_scope(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        with cc.scope():
            cc.assert_equal(a, b)
            self.assertTrue(cc.are_equal(a, b))
        self.assertFalse(cc.are_equal(a, b))
        # exceptions inside the block still pop exactly one scope
        with self.assertRaises(ContradictionError):
            with cc.scope():
                cc.assert_distinct(a, b)
                with cc.scope():
                    cc.assert_equal(a, b)  # conflicts with inner distinct
        self.assertEqual(cc.scope_depth, 0)
        self.assertFalse(cc.are_equal(a, b))
        self.assertEqual(cc.distinct_assertions, ())


class TestScopeHandles(unittest.TestCase):
    def test_inner_handles_invalidated_after_pop(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        cc.push()
        ga = cc.add_term("g", [a])
        cc.assert_equal(a, ga)
        cc.pop()
        # every use of the inner handle now fails
        with self.assertRaises(StaleNodeError):
            cc.are_equal(ga, a)
        with self.assertRaises(StaleNodeError):
            cc.term_of(ga)
        with self.assertRaises(StaleNodeError):
            cc.explain(ga, ga)
        # StaleNodeError is an UnknownNodeError for backward compatibility
        with self.assertRaises(UnknownNodeError):
            cc.assert_equal(ga, a)

    def test_same_shape_term_after_pop_gets_fresh_id(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        cc.push()
        ga_old = cc.add_term("g", [a])
        cc.pop()
        ga_new = cc.add_term("g", [a])
        self.assertNotEqual(ga_old, ga_new)
        # the old handle must not silently alias the new same-shape term
        with self.assertRaises(StaleNodeError):
            cc.are_equal(ga_old, ga_new)
        self.assertTrue(cc.are_equal(ga_new, ga_new))
        # outer handles are unaffected
        self.assertTrue(cc.are_equal(a, a))

    def test_push_does_not_copy_term_graph(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        cc.add_term("f", [a])
        terms_obj = cc._terms
        hashcons_obj = cc._hashcons
        cc.push()
        # push is O(1): same objects, empty journal
        self.assertIs(cc._terms, terms_obj)
        self.assertIs(cc._hashcons, hashcons_obj)
        self.assertEqual(cc._scopes[-1].journal, {})
        cc.pop()


class TestScopeConflicts(unittest.TestCase):
    def test_conflict_scope_still_poppable(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.push()
        cc.assert_distinct(fa, fb)
        with self.assertRaises(ContradictionError) as ctx:
            cc.assert_equal(a, b)  # congruence would equate f(a), f(b)
        err = ctx.exception
        self.assertTrue(
            verify_contradiction(err.proof, err.inputs, err.distincts,
                                 err.terms))
        # the conflicted scope is still usable and poppable
        self.assertFalse(cc.are_equal(a, b))
        cc.pop()
        # conflict state (the inner distinct) is gone with the scope
        self.assertEqual(cc.distinct_assertions, ())
        cc.assert_equal(a, b)
        self.assertTrue(cc.are_equal(fa, fb))

    def test_inner_distinct_does_not_leak(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        cc.push()
        cc.assert_distinct(a, b)
        cc.push()
        cc.assert_distinct(a, b)  # same pair again at a deeper level
        cc.pop()
        cc.pop()
        # both layers of the distinct assertion are gone
        cc.assert_equal(a, b)
        self.assertTrue(cc.are_equal(a, b))

    def test_batch_inside_scope_rolls_back_then_pops(self):
        cc = CongruenceClosure()
        a, b, c, d = (cc.add_term(n) for n in "abcd")
        cc.push()
        cc.assert_distinct(c, d)
        with self.assertRaises(ContradictionError):
            cc.apply_batch([("=", a, b), ("=", b, c), ("=", a, d)])
        self.assertFalse(cc.are_equal(a, b))
        cc.pop()
        self.assertEqual(cc.input_equalities, ())
        self.assertEqual(cc.distinct_assertions, ())


class TestScopeProofs(unittest.TestCase):
    def test_proof_after_pop_uses_only_outer_edges(self):
        cc = CongruenceClosure()
        a, b, c = (cc.add_term(n) for n in "abc")
        cc.assert_equal(a, b)
        cc.push()
        cc.assert_equal(b, c)
        inner_proof = cc.explain(a, c)
        self.assertEqual(len(inner_proof), 2)  # uses both input edges
        cc.pop()
        # outer conclusion a = b is still provable, from the outer edge only
        proof = cc.explain(a, b)
        self.assertEqual(proof, (("input", a, b),))
        self.assertTrue(
            verify_proof(proof, a, b, cc.input_equalities, cc.terms))
        # the popped inner proof no longer verifies against live inputs
        self.assertEqual(cc.input_equalities, ((a, b),))

    def test_explain_inside_scope_uses_inner_assertions(self):
        cc = CongruenceClosure()
        a = cc.add_term("a")
        b = cc.add_term("b")
        fa = cc.add_term("f", [a])
        fb = cc.add_term("f", [b])
        cc.push()
        cc.assert_equal(a, b)
        proof = cc.explain(fa, fb)
        leaves = list(proof_input_leaves(proof))
        self.assertEqual(leaves, [(a, b)])  # the inner assertion
        self.assertTrue(
            verify_proof(proof, fa, fb, cc.input_equalities, cc.terms))
        cc.pop()


class TestScopePrefixCrossCheck(unittest.TestCase):
    """Replay every operation prefix's live assertions into a fresh
    instance and compare; independently check proof leaf levels."""

    def check_prefix(self, cc, items):
        """items: the currently live ("term", nid) / ("op", (rel, x, y))
        entries, maintained by the caller with stack-aligned truncation."""
        live_terms = [t for (kind, t) in items if kind == "term"]
        live_ops = [payload for (kind, payload) in items if kind == "op"]
        # assertion views must match the live operations exactly
        self.assertEqual(cc.input_equalities,
                         tuple((x, y) for rel, x, y in live_ops if rel == "="))
        self.assertEqual(cc.distinct_assertions,
                         tuple((x, y) for rel, x, y in live_ops if rel == "!="))
        # replay into a brand-new closure
        fresh = CongruenceClosure()
        id_map = {}
        for t in live_terms:
            func, args = cc.term_of(t)
            id_map[t] = fresh.add_term(func, [id_map[x] for x in args])
        for rel, x, y in live_ops:
            if rel == "=":
                fresh.assert_equal(id_map[x], id_map[y])
            else:
                fresh.assert_distinct(id_map[x], id_map[y])
        live_inputs = {_norm(x, y) for rel, x, y in live_ops if rel == "="}
        for x in live_terms:
            for y in live_terms:
                expected = fresh.are_equal(id_map[x], id_map[y])
                self.assertEqual(cc.are_equal(x, y), expected,
                                 f"prefix mismatch on ({x}, {y})")
                if expected:
                    proof = cc.explain(x, y)
                    self.assertTrue(
                        verify_proof(proof, x, y, cc.input_equalities,
                                     cc.terms))
                    # every proof leaf must be a currently live assertion
                    # (no revoked edge may prove an outer conclusion)
                    for u, v in proof_input_leaves(proof):
                        self.assertIn(_norm(u, v), live_inputs)
                else:
                    with self.assertRaises(NotEqualError):
                        cc.explain(x, y)

    def test_every_prefix_matches_fresh_instance(self):
        cc = CongruenceClosure()
        items = []  # ("term", nid) / ("op", (rel, x, y)) currently live
        marks = []  # len(items) at each push, for stack-aligned truncation

        def add(func, args=()):
            nid = cc.add_term(func, args)
            items.append(("term", nid))
            self.check_prefix(cc, items)
            return nid

        def op(rel, x, y):
            if rel == "=":
                redundant = cc.are_equal(x, y)  # not recorded by the library
                cc.assert_equal(x, y)
                if redundant:
                    self.check_prefix(cc, items)
                    return
            else:
                cc.assert_distinct(x, y)
            items.append(("op", (rel, x, y)))
            self.check_prefix(cc, items)

        def push():
            marks.append(len(items))
            cc.push()
            self.check_prefix(cc, items)

        def pop():
            cc.pop()
            del items[marks.pop():]
            self.check_prefix(cc, items)

        a = add("a")
        b = add("b")
        c = add("c")
        fa = add("f", [a])
        fb = add("f", [b])
        gfa = add("g", [fa])
        gfb = add("g", [fb])
        op("!=", gfa, gfb)          # base-level distinct
        push()                       # level 1
        op("=", a, c)
        hfa = add("h", [fa])
        hfb = add("h", [fb])
        push()                       # level 2
        op("!=", hfa, hfb)           # inner-level distinct
        # f(a) = f(b) would congruence-close to g(f(a)) = g(f(b)),
        # violating the base-level distinct: must conflict
        with self.assertRaises(ContradictionError) as ctx:
            cc.assert_equal(fa, fb)
        err = ctx.exception
        self.assertTrue(
            verify_contradiction(err.proof, err.inputs, err.distincts,
                                 err.terms))
        self.check_prefix(cc, items)  # failed op left no trace
        pop()                          # conflicted layer pops cleanly
        self.assertTrue(cc.are_equal(gfa, gfb) is False)
        pop()                          # back to base
        self.assertFalse(cc.are_equal(a, c))
        # inner handles hfa/hfb are stale now
        with self.assertRaises(StaleNodeError):
            cc.are_equal(hfa, hfb)
        # base-level distinct is still enforced
        with self.assertRaises(ContradictionError):
            cc.assert_equal(a, b)
        self.check_prefix(cc, items)

    def test_random_push_pop_sequences(self):
        for seed in range(20):
            rng = random.Random(1000 + seed)
            cc = CongruenceClosure()
            items = []
            marks = []
            for i in range(3):
                nid = cc.add_term(f"c{i}")
                items.append(("term", nid))
            for _ in range(60):
                live_terms = [t for (kind, t) in items if kind == "term"]
                action = rng.randrange(6)
                if action == 0 and cc.scope_depth < 4:
                    marks.append(len(items))
                    cc.push()
                elif action == 1 and cc.scope_depth > 0:
                    cc.pop()
                    del items[marks.pop():]
                elif action == 2:
                    f = rng.choice(["f", "g"])
                    try:
                        nid = cc.add_term(f, [rng.choice(live_terms)])
                    except ContradictionError:
                        pass  # auto-merge conflict: addition rolled back
                    else:
                        items.append(("term", nid))
                elif action in (3, 4):
                    x, y = rng.choice(live_terms), rng.choice(live_terms)
                    redundant = cc.are_equal(x, y)  # not recorded by cc
                    try:
                        cc.assert_equal(x, y)
                    except ContradictionError:
                        pass
                    else:
                        if not redundant:
                            items.append(("op", ("=", x, y)))
                else:
                    x, y = rng.choice(live_terms), rng.choice(live_terms)
                    try:
                        cc.assert_distinct(x, y)
                    except ContradictionError:
                        pass
                    else:
                        items.append(("op", ("!=", x, y)))
                self.check_prefix(cc, items)


if __name__ == "__main__":
    unittest.main()
