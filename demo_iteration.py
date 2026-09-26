"""Deterministic offline demo of injective function symbols.

Shows the new iteration behavior on top of congruence_closure.py:
backward argument propagation from declared-injective functions, chaining
with forward congruence, and a contradiction against a distinct assertion
whose proof is replayed by the independent verifier.  No sleeps, no
recorded output; everything is computed live in well under 90 seconds.
"""

from congruence_closure import (
    CongruenceClosure,
    ContradictionError,
    NotEqualError,
    proof_to_str,
    term_to_str,
    verify_contradiction,
    verify_proof,
)


def normal_scenario():
    print("=== 1. Normal: injective backward + congruence forward chaining ===")
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
    cc.declare_injective("f")

    cc.assert_equal(hfa, hfb)
    print("asserted h(f(a)) = h(f(b)) with h, f injective")
    print("derived f(a) = f(b):", cc.are_equal(fa, fb), "(backward, h)")
    print("derived a = b:", cc.are_equal(a, b), "(backward, f)")
    print("derived g(f(a)) = g(f(b)):", cc.are_equal(gfa, gfb),
          "(forward congruence)")

    proof = cc.explain(a, b)
    print("proof of a = b:")
    print(proof_to_str(proof, cc.terms))
    ok = verify_proof(proof, a, b, cc.input_equalities, cc.terms,
                      cc.injective_functions)
    print("independent verification:", ok)

    print()
    print("=== 2. Normal: binary injective, arguments swapped ===")
    cc2 = CongruenceClosure()
    x = cc2.add_term("x")
    y = cc2.add_term("y")
    g1 = cc2.add_term("g", [x, y])
    g2 = cc2.add_term("g", [y, x])
    cc2.declare_injective("g")
    cc2.assert_equal(g1, g2)
    print("asserted g(x, y) = g(y, x) with g injective")
    print("derived x = y:", cc2.are_equal(x, y), "(position-wise backward)")

    print()
    print("=== 3. Boundary: undeclared function stays one-directional ===")
    cc3 = CongruenceClosure()
    u = cc3.add_term("u")
    v = cc3.add_term("v")
    su = cc3.add_term("s", [u])
    sv = cc3.add_term("s", [v])
    cc3.assert_equal(su, sv)
    print("asserted s(u) = s(v), s NOT declared injective")
    print("u = v derived:", cc3.are_equal(u, v), "(must be False)")
    try:
        cc3.explain(u, v)
    except NotEqualError as err:
        print("explain(u, v) correctly refused:", err)


def rejection_scenario():
    print()
    print("=== 4. Rejection boundary: injectivity contradicts distinctness ===")
    cc = CongruenceClosure()
    a = cc.add_term("a")
    b = cc.add_term("b")
    fa = cc.add_term("f", [a])
    fb = cc.add_term("f", [b])
    cc.declare_injective("f")
    cc.assert_distinct(a, b)
    try:
        cc.assert_equal(fa, fb)  # would force a = b via injectivity
    except ContradictionError as err:
        print("assertion rejected:", err)
        print("contradiction proof:")
        print(proof_to_str(err.proof, err.terms))
        ok = verify_contradiction(err.proof, err.inputs, err.distincts,
                                  err.terms, err.injective)
        print("independent verification of contradiction proof:", ok)
    t_fa = term_to_str(fa, cc.terms)
    t_fb = term_to_str(fb, cc.terms)
    print("after rollback:", t_fa, "=", t_fb, "is", cc.are_equal(fa, fb),
          "(must be False); a = b is", cc.are_equal(a, b), "(must be False)")


def main():
    normal_scenario()
    rejection_scenario()
    print()
    print("demo_iteration finished.")


if __name__ == "__main__":
    main()
