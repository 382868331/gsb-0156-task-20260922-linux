"""Deterministic offline demo of the congruence_closure module.

Runs a normal scenario (multi-layer congruence + verified proof) and then
deliberately triggers two rejection boundaries (a contradiction with
batch rollback, and invalid input).  No sleeps, no recorded output.
"""

from congruence_closure import (
    CongruenceClosure,
    ContradictionError,
    ValidationError,
    proof_to_str,
    term_to_str,
    verify_contradiction,
    verify_proof,
)
from boolean_solver import (
    And,
    AtomLimitError,
    BooleanSolver,
    Not,
    Or,
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


def boolean_scenario():
    print("\n=== 4. Boolean layer: and/or/not + disequality, SAT ===")
    solver = BooleanSolver()
    a = solver.add_term("a")
    b = solver.add_term("b")
    c = solver.add_term("c")
    fa = solver.add_term("f", [a])
    fb = solver.add_term("f", [b])
    e_ab = solver.eq(a, b)
    e_bc = solver.eq(b, c)
    e_ac = solver.eq(a, c)  # ne(a, c) below shares this atom

    formula = And(Or(e_ab, e_bc), solver.ne(a, c))
    result = solver.solve(formula)
    print("formula: (a=b OR b=c) AND a!=c")
    print("status:", result.status)
    print("satisfying assignment:", solver.format_assignment(result))
    print("equality environments rebuilt and tested:",
          result.environments_tested)

    print("\n=== 5. Boolean layer: UNSAT via transitivity / congruence ===")
    r1 = solver.solve(And(e_ab, e_bc, solver.ne(a, c)))
    print("(a=b AND b=c AND a!=c):", r1.status,
          "(transitivity forbids it)")
    r2 = solver.solve(And(e_ab, solver.ne(fa, fb)))
    print("(a=b AND f(a)!=f(b)):", r2.status,
          "(congruence forces f(a)=f(b))")

    # Branch isolation: solving never touches the shared term store.
    print("shared term store nodes after all solves:", solver.node_count,
          "(unchanged; branches rebuild fresh environments)")

    print("\n=== 6. Rejection boundary: atom limit and invalid formula ===")
    s2 = BooleanSolver()  # at most 8 distinct boolean atoms
    ids = [s2.add_term(f"v{i}") for i in range(9)]
    try:
        for i in range(9):
            s2.eq(ids[i], ids[(i + 1) % 9])  # the 9th pair is a 9th atom
    except AtomLimitError as err:
        print(f"atom limit rejected: {err}")
    print("atoms tracked after rejection:", s2.atom_count,
          "(no half-updated state)")
    try:
        solver.solve("a = b")  # not a Formula
    except ValidationError as err:
        print(f"invalid formula rejected: {err}")


def main():
    normal_scenario()
    rejection_scenario()
    boolean_scenario()
    print("\ndemo finished.")


if __name__ == "__main__":
    main()
