"""Deterministic offline demo of the congruence_closure module.

Runs normal scenarios (multi-layer congruence with verified proof; boolean
AND/OR/NOT solving over equality atoms) and then deliberately triggers
rejection boundaries (a contradiction with batch rollback, an impossible
boolean branch, the 8-atom enumeration boundary, and invalid input).  No
sleeps, no recorded output.
"""

from congruence_closure import (
    MAX_BOOLEAN_ATOMS,
    AtomLimitError,
    BooleanSolver,
    CongruenceClosure,
    ContradictionError,
    ValidationError,
    land,
    lnot,
    lor,
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


def rejection_scenario():
    print("\n=== 2. Rejection boundary: batch conflict, rolled back ===")
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

    print("\n=== 3. Rejection boundary: invalid input is located ===")
    try:
        cc.assert_equal(a, True)  # bool is not a valid node id
    except ValidationError as err:
        print(f"invalid input rejected: {err}")


def boolean_normal_scenario():
    print("\n=== 4. Boolean layer: AND/OR/NOT over equality atoms ===")
    # Hand-built puzzle over constants a, b, c:
    #   p: a = b, q: b = c, r: a = c
    # ask for (p or q) and not r.
    # Hand analysis: r false means a != c; exactly one of the two links may
    # hold (both would transitively force a = c).  Two models expected.
    sol = BooleanSolver()
    a, b, c = (sol.add_term(n) for n in "abc")
    p = sol.add_atom(a, b)
    q = sol.add_atom(b, c)
    r = sol.add_atom(a, c)
    names = ("a=b", "b=c", "a=c")
    formula = land(lor(p, q), lnot(r))
    models = sol.all_models(formula)
    for m in models:
        print("model:", ", ".join(
            f"{names[i]}={'true' if v else 'false'}" for i, v in enumerate(m)))

    # Rebuild one model and query it: a = b must hold, a = c must not.
    cc = sol.build_environment(models[0])
    print(f"in the first model: a = b is {cc.are_equal(a, b)}, "
          f"a = c is {cc.are_equal(a, c)}")
    # Solver template was never asserted into: solve() stays repeatable.
    again = sol.all_models(formula)
    print("repeated enumeration gives the same models:", again == models)


def boolean_unsat_scenario():
    print("\n=== 5. Boolean rejection: congruence makes a branch impossible ===")
    # a = b AND f(a) != f(b): congruence rules out the only candidate.
    sol = BooleanSolver()
    a, b = sol.add_term("a"), sol.add_term("b")
    fa, fb = sol.add_term("f", [a]), sol.add_term("f", [b])
    p = sol.add_atom(a, b)
    q = sol.add_atom(fa, fb)
    result = sol.solve(land(p, lnot(q)))
    print("formula (a = b) and not (f(a) = f(b)) satisfiable:",
          result.satisfiable, "(must be False)")
    # The reverse direction IS allowed: f(a) = f(b) does not force a = b.
    rev = sol.solve(land(q, lnot(p)))
    print("formula (f(a) = f(b)) and not (a = b) satisfiable:",
          rev.satisfiable, "with assignment", rev.assignment,
          "(congruence is one-directional)")


def boolean_boundary_scenario():
    print(f"\n=== 6. Boundary: {MAX_BOOLEAN_ATOMS} atoms, full truth table ===")
    sol = BooleanSolver()
    consts = [sol.add_term(f"c{i}") for i in range(8)]
    for i in range(7):
        sol.add_atom(consts[i], consts[i + 1])
    sol.add_atom(consts[0], consts[7])  # endpoint atom, index 7
    import time
    t0 = time.perf_counter()
    # Every row of the 256-row table is a candidate here; rows where the
    # seven links chain c0..c7 together while atom 7 is false are rejected.
    models = sol.all_models(lor(*range(MAX_BOOLEAN_ATOMS)))
    elapsed = time.perf_counter() - t0
    print(f"enumerated {len(models)} satisfying assignments in "
          f"{elapsed*1000:.1f} ms (255 candidate environments rebuilt; "
          f"8 are ruled out by transitivity/congruence)")
    chain = land(*range(7), lnot(7))
    print("seven links + endpoint distinctness satisfiable:",
          bool(sol.solve(chain)), "(must be False; transitively equal)")


def boolean_error_scenario():
    print("\n=== 7. Boolean rejection boundaries: explicit errors ===")
    sol = BooleanSolver()
    consts = [sol.add_term(f"c{i}") for i in range(9)]
    for i in range(MAX_BOOLEAN_ATOMS):
        sol.add_atom(consts[i], consts[i + 1])
    try:
        sol.add_atom(consts[0], consts[8])
    except AtomLimitError as err:
        print(f"9th atom rejected: {err}")
    print("atom count after the failed registration:", sol.atom_count,
          "(must still be 8; no partial state)")

    try:
        sol.solve(("xor", 0, 1))
    except ValidationError as err:
        print(f"malformed formula rejected: {err}")

    # An explicitly inconsistent assignment is refused by build_environment:
    # u = v true while g(u) = g(v) false contradicts congruence.
    small = BooleanSolver()
    u = small.add_term("u")
    v = small.add_term("v")
    gu = small.add_term("g", [u])
    gv = small.add_term("g", [v])
    small.add_atom(u, v)
    small.add_atom(gu, gv)
    try:
        small.build_environment((True, False))
    except ContradictionError as err:
        print(f"inconsistent assignment rejected: {err}")


def main():
    normal_scenario()
    rejection_scenario()
    boolean_normal_scenario()
    boolean_unsat_scenario()
    boolean_boundary_scenario()
    boolean_error_scenario()
    print("\ndemo finished.")


if __name__ == "__main__":
    main()
