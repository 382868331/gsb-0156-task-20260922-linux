"""Independent checker for congruence-closure proof trees.

This module deliberately does not import the engine.  A proof is a nested
tuple tree over structural terms, where a structural term is
``(symbol, (subterm, ...))`` (a constant is ``(symbol, ())``):

* ``("input", k)``            -- the k-th input equality (0-based)
* ``("cong", symbol, subs)``  -- congruence: f(a_i...) == f(b_i...) from a_i == b_i
* ``("trans", p, q)``         -- transitivity
* ``("symm", p)``             -- symmetry
* ``("refl", term)``          -- reflexivity of a structural term

``verify_proof`` recomputes the proved equation purely from the tree and the
list of input equalities; it never trusts the proof to state its own
conclusion.
"""

from __future__ import annotations

import sys
from contextlib import contextmanager

__all__ = ["InvalidProofError", "verify_proof"]


class InvalidProofError(ValueError):
    """A proof tree is malformed or does not check out."""


@contextmanager
def _recursion_guard(min_limit):
    old = sys.getrecursionlimit()
    if old >= min_limit:
        yield
        return
    sys.setrecursionlimit(min_limit)
    try:
        yield
    finally:
        sys.setrecursionlimit(old)


def _check_struct(term, path="term"):
    if not (isinstance(term, tuple) and len(term) == 2
            and isinstance(term[0], str) and term[0]
            and isinstance(term[1], tuple)):
        raise InvalidProofError(f"malformed structural term at {path}: {term!r}")
    for i, sub in enumerate(term[1]):
        _check_struct(sub, f"{path}[1][{i}]")


def verify_proof(proof, input_equalities):
    """Check ``proof`` and return the ``(lhs, rhs)`` structural terms it proves.

    ``input_equalities`` is a sequence of ``(lhs, rhs)`` structural-term
    pairs; ``("input", k)`` refers to ``input_equalities[k]``.  Raises
    :class:`InvalidProofError` on any malformed node or mismatched
    transitivity step.
    """
    if not isinstance(input_equalities, (list, tuple)):
        raise InvalidProofError(
            f"input_equalities must be a list or tuple, got "
            f"{type(input_equalities).__name__}")
    with _recursion_guard(100_000):
        return _verify(proof, input_equalities, "proof")


def _verify(proof, inputs, path):
    if not (isinstance(proof, tuple) and len(proof) >= 1
            and isinstance(proof[0], str)):
        raise InvalidProofError(f"malformed proof node at {path}: {proof!r}")
    tag = proof[0]

    if tag == "input":
        if len(proof) != 2 or isinstance(proof[1], bool) \
                or not isinstance(proof[1], int):
            raise InvalidProofError(
                f"'input' node needs an integer index at {path}: {proof!r}")
        k = proof[1]
        if not 0 <= k < len(inputs):
            raise InvalidProofError(
                f"input index {k} out of range at {path} "
                f"({len(inputs)} input equalities)")
        pair = inputs[k]
        if not (isinstance(pair, (list, tuple)) and len(pair) == 2):
            raise InvalidProofError(
                f"input_equalities[{k}] is not a pair: {pair!r}")
        _check_struct(pair[0], f"input_equalities[{k}][0]")
        _check_struct(pair[1], f"input_equalities[{k}][1]")
        return (pair[0], pair[1])

    if tag == "symm":
        if len(proof) != 2:
            raise InvalidProofError(f"'symm' node needs 1 child at {path}")
        lhs, rhs = _verify(proof[1], inputs, f"{path}[1]")
        return (rhs, lhs)

    if tag == "trans":
        if len(proof) != 3:
            raise InvalidProofError(f"'trans' node needs 2 children at {path}")
        l1, r1 = _verify(proof[1], inputs, f"{path}[1]")
        l2, r2 = _verify(proof[2], inputs, f"{path}[2]")
        if r1 != l2:
            raise InvalidProofError(
                f"'trans' midpoint mismatch at {path}: {r1!r} != {l2!r}")
        return (l1, r2)

    if tag == "cong":
        if len(proof) != 3 or not isinstance(proof[1], str) or not proof[1] \
                or not isinstance(proof[2], (tuple, list)):
            raise InvalidProofError(
                f"malformed 'cong' node at {path}: {proof!r}")
        parts = [_verify(s, inputs, f"{path}[2][{i}]")
                 for i, s in enumerate(proof[2])]
        lhs = (proof[1], tuple(p[0] for p in parts))
        rhs = (proof[1], tuple(p[1] for p in parts))
        return (lhs, rhs)

    if tag == "refl":
        if len(proof) != 2:
            raise InvalidProofError(f"'refl' node needs 1 child at {path}")
        _check_struct(proof[1], f"{path}[1]")
        return (proof[1], proof[1])

    raise InvalidProofError(f"unknown proof node tag {tag!r} at {path}")
