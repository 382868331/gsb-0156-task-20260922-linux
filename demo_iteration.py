"""Deterministic offline demo of injective function reasoning.

Shows a normal scenario (nested injective functions whose equal outputs
force equal arguments, with an independently verified proof) and boundary
scenarios (a distinctness contradiction with rollback, and an undeclared
function that must not reverse-infer).  No sleeps, no recorded output.
"""

from congruence_closure import (
    CongruenceClosure,
    ContradictionError,
    proof_to_str,
    term_to_str,
    verify_contradiction,
    verify_proof,
)


def normal_scenario():
    print("=== 1. Normal: injective outputs force equal arguments ===")
    cc = CongruenceClosure()
    a = cc.add_term("a")
    b = cc.add_term("b")
    fa = cc.add_term("f", [a])
    fb = cc.add_term("f", [b])
    gfa = cc.add_term("g", [fa])
    gfb = cc.add_term("g", [fb])
    cc.declare_injective("f")
    cc.declare_injective("g")

    cc.assert_equal(gfa, gfb)
    print("declared injective:", ", ".join(cc.injective_symbols))
    print("asserted g(f(a)) = g(f(b)); derived a = b:",
          cc.are_equal(a, b))

    proof = cc.explain(a, b)
    print("proof:")
    print(proof_to_str(proof, cc.terms))
    ok = verify_proof(proof, a, b, cc.input_equalities, cc.terms,
                      cc.injective_symbols)
    print("independent verification of proof:", ok)


def boundary_scenarios():
    print("\n=== 2. Boundary: injectivity contradicts a distinct pair ===")
    cc = CongruenceClosure()
    a = cc.add_term("a")
    b = cc.add_term("b")
    fa = cc.add_term("f", [a])
    fb = cc.add_term("f", [b])
    cc.declare_injective("f")
    cc.assert_distinct(a, b)
    try:
        cc.assert_equal(fa, fb)
    except ContradictionError as err:
        print(f"assertion rejected: {err}")
        print("contradiction proof:")
        print(proof_to_str(err.proof, err.terms))
        ok = verify_contradiction(err.proof, err.inputs, err.distincts,
                                  err.terms, err.injectives)
        print("independent verification of contradiction proof:", ok)
    print("after rollback: f(a) = f(b) is", cc.are_equal(fa, fb),
          "(must be False); a = b is", cc.are_equal(a, b),
          "(must be False)")

    print("\n=== 3. Boundary: undeclared function stays one-directional ===")
    cc2 = CongruenceClosure()
    x = cc2.add_term("x")
    y = cc2.add_term("y")
    fx = cc2.add_term("f", [x])
    fy = cc2.add_term("f", [y])
    cc2.assert_equal(fx, fy)
    t_fx, t_fy = term_to_str(fx, cc2.terms), term_to_str(fy, cc2.terms)
    print(f"asserted {t_fx} = {t_fy} without declaring f injective;")
    print("reverse inference x = y holds:", cc2.are_equal(x, y),
          "(must be False)")


def main():
    normal_scenario()
    boundary_scenarios()
    print("\ndemo_iteration finished.")


if __name__ == "__main__":
    main()
