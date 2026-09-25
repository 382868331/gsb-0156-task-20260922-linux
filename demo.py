"""Deterministic offline demo of the congruence_closure module.

Runs a normal scenario (multi-layer congruence + verified proof), a scoped
assumption scenario (push/pop with handle invalidation), and then
deliberately triggers rejection boundaries (a contradiction with batch
rollback, invalid input, and popping at the base level).  No sleeps, no
recorded output.
"""

from congruence_closure import (
    CongruenceClosure,
    ContradictionError,
    ScopeError,
    StaleNodeError,
    ValidationError,
    proof_to_str,
    term_to_str,
    verify_contradiction,
    verify_proof,
)


def normal_scenario():
    print("=== 1. Normal: multi-layer congruence with verified proof ===")
    cc = CongruenceClosure()
    a = cc.add_term("a")
    b = cc.add_term("b")
    fa = cc.add_term("f", [a])
    fb = cc.add_term("f", [b])
    gfa = cc.add_term("g", [fa])
    gfb = cc.add_term("g", [fb])

    cc.assert_equal(a, b)
    t_gfa, t_gfb = term_to_str(gfa, cc.terms), term_to_str(gfb, cc.terms)
    print(f"asserted a = b; derived {t_gfa} = {t_gfb}:",
          cc.are_equal(gfa, gfb))

    proof = cc.explain(gfa, gfb)
    print("proof:")
    print(proof_to_str(proof, cc.terms))
    ok = verify_proof(proof, gfa, gfb, cc.input_equalities, cc.terms)
    print("independent verification of proof:", ok)

    # Congruence is one-directional: f(a) = f(b) never implies a = b.
    cc2 = CongruenceClosure()
    x = cc2.add_term("x")
    y = cc2.add_term("y")
    fx = cc2.add_term("f", [x])
    fy = cc2.add_term("f", [y])
    cc2.assert_equal(fx, fy)
    print(f"asserted f(x) = f(y); reverse inference x = y holds:",
          cc2.are_equal(x, y), "(must be False)")


def scoped_scenario():
    print("\n=== 2. Scoped assumptions: push / pop ===")
    cc = CongruenceClosure()
    a = cc.add_term("a")
    b = cc.add_term("b")
    fa = cc.add_term("f", [a])
    fb = cc.add_term("f", [b])
    gfa = cc.add_term("g", [fa])
    gfb = cc.add_term("g", [fb])

    cc.push()
    print(f"pushed assumption scope (depth {cc.scope_depth})")
    cc.assert_equal(a, b)  # hypothesis: valid only inside this scope
    print("under the hypothesis, g(f(a)) = g(f(b)) derived:",
          cc.are_equal(gfa, gfb))
    proof = cc.explain(gfa, gfb)
    print("proof inside the scope:")
    print(proof_to_str(proof, cc.terms))
    ok = verify_proof(proof, gfa, gfb, cc.input_equalities, cc.terms)
    print("independent verification of scoped proof:", ok)

    cc.pop()
    print(f"popped (depth {cc.scope_depth}); hypothesis withdrawn")
    print("after pop: a = b is", cc.are_equal(a, b),
          "(must be False); g(f(a)) = g(f(b)) is",
          cc.are_equal(gfa, gfb), "(must be False)")
    print("assertion lists back to outer state:",
          cc.input_equalities == () and cc.distinct_assertions == ())

    # Handles created inside the popped scope are invalidated.
    cc.push()
    inner = cc.add_term("h", [a])
    cc.pop()
    try:
        cc.are_equal(inner, a)
    except StaleNodeError as err:
        print(f"stale inner handle rejected: {err}")
    rebuilt = cc.add_term("h", [a])  # same shape, fresh id
    print(f"same-shape term rebuilt with fresh id {rebuilt} "
          f"(old id {inner} stays invalid):", rebuilt != inner)

    # A conflicted scope can still be popped, and the conflict dies with it.
    cc.push()
    cc.assert_distinct(fa, fb)
    try:
        cc.assert_equal(a, b)  # congruence would equate f(a) and f(b)
    except ContradictionError as err:
        print(f"inner conflict raised: {err}")
    cc.pop()
    print("conflicted scope popped; distinct assertion is gone:",
          cc.distinct_assertions == ())


def rejection_scenario():
    print("\n=== 3. Rejection boundary: batch conflict, rolled back ===")
    cc = CongruenceClosure()
    a = cc.add_term("a")
    b = cc.add_term("b")
    fa = cc.add_term("f", [a])
    fb = cc.add_term("f", [b])
    cc.assert_distinct(fa, fb)
    try:
        cc.apply_batch([("=", a, b)])  # congruence would force f(a) = f(b)
    except ContradictionError as err:
        print(f"batch rejected: {err}")
        print("contradiction proof:")
        print(proof_to_str(err.proof, err.terms))
        ok = verify_contradiction(err.proof, err.inputs, err.distincts,
                                  err.terms)
        print("independent verification of contradiction proof:", ok)
    print("after rollback: a = b is", cc.are_equal(a, b),
          "(must be False); f(a) = f(b) is", cc.are_equal(fa, fb),
          "(must be False)")

    print("\n=== 4. Rejection boundary: invalid input is located ===")
    try:
        cc.assert_equal(a, True)  # bool is not a valid node id
    except ValidationError as err:
        print(f"invalid input rejected: {err}")

    print("\n=== 5. Rejection boundary: pop at base level ===")
    try:
        cc.pop()  # no scope is open
    except ScopeError as err:
        print(f"base-level pop rejected: {err}")
    print("base state unchanged: f(a) = f(b) is", cc.are_equal(fa, fb),
          "(must be False)")


def main():
    normal_scenario()
    scoped_scenario()
    rejection_scenario()
    print("\ndemo finished.")


if __name__ == "__main__":
    main()
