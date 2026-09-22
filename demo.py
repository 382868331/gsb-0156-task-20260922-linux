"""Deterministic demo of the congruence_closure package.

Runs entirely offline with fixed inputs.  Prints:
  1. a normal result: multi-level congruence f(g(a)) == f(g(b)) derived from
     the single input a == b, with the proof verified by the independent
     checker;
  2. that f(c) == f(d) does NOT imply c == d (no reverse inference);
  3. an actually triggered rejection boundary: a batch whose equalities
     violate an assert_distinct constraint -> ConflictError, the conflict
     proof verified independently, and the batch fully rolled back;
  4. an invalid-input rejection (NaN as a term id).
"""

from congruence_closure import (
    CongruenceClosure,
    ConflictError,
    InvalidInputError,
    verify_proof,
)


def main():
    cc = CongruenceClosure()

    a = cc.add_term("a")
    b = cc.add_term("b")
    c = cc.add_term("c")
    d = cc.add_term("d")
    ga = cc.add_term("g", [a])
    gb = cc.add_term("g", [b])
    fga = cc.add_term("f", [ga])
    fgb = cc.add_term("f", [gb])

    # --- 1. normal case: one input equality, two congruence levels ---------
    cc.assert_equal(a, b)
    print("[1] asserted a == b")
    print("    f(g(a)) == f(g(b)) ?", cc.are_equal(fga, fgb))
    proof = cc.explain(fga, fgb)
    lhs, rhs = verify_proof(proof, cc.input_equalities())
    ok = (lhs == cc.term_structure(fga) and rhs == cc.term_structure(fgb))
    print("    proof:", proof)
    print("    independent verify_proof: endpoints match =", ok)

    # --- 2. no reverse inference -------------------------------------------
    hc = cc.add_term("h", [c])
    hd = cc.add_term("h", [d])
    cc.assert_equal(hc, hd)
    print("[2] asserted h(c) == h(d); c == d derivable?", cc.are_equal(c, d))

    # --- 3. rejection boundary: batch conflicts with assert_distinct -------
    cc.assert_distinct(c, d)
    k = cc.add_term("k")
    classes_before = cc.class_count
    print("[3] asserted c != d; now submitting batch "
          "[(c, k), (k, d)] which forces c == d ...")
    try:
        cc.assert_batch(equalities=[(c, k), (k, d)])
        print("    UNEXPECTED: batch accepted")
    except ConflictError as exc:
        lhs, rhs = verify_proof(exc.proof, exc.input_equalities)
        ok = {lhs, rhs} == {cc.term_structure(c), cc.term_structure(d)}
        print("    ConflictError:", exc)
        print("    conflict proof verifies standalone:", ok)
        print("    rolled back: c == k ?", cc.are_equal(c, k),
              "| c == d ?", cc.are_equal(c, d),
              "| class_count restored ?", cc.class_count == classes_before)

    # --- 4. invalid input rejection -----------------------------------------
    try:
        cc.are_equal(float("nan"), a)
        print("    UNEXPECTED: NaN accepted")
    except InvalidInputError as exc:
        print("[4] InvalidInputError as specified:", exc)


if __name__ == "__main__":
    main()
