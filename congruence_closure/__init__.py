"""Congruence closure for ground equations over function symbols.

Public interface:

* :class:`CongruenceClosure` -- the engine (add_term / assert_equal /
  assert_distinct / assert_batch / explain / are_equal).
* :func:`verify_proof` -- independent checker for the proof trees returned
  by ``explain`` and carried by :class:`ConflictError`.
* Error types: :class:`CongruenceClosureError` (base),
  :class:`InvalidInputError`, :class:`LimitExceededError`,
  :class:`BudgetExhaustedError`, :class:`NotEqualError`,
  :class:`ConflictError`, :class:`InvalidProofError`.
"""

from .core import (
    DEFAULT_MAX_TERMS,
    DEFAULT_WORK_BUDGET,
    BudgetExhaustedError,
    CongruenceClosure,
    CongruenceClosureError,
    ConflictError,
    InvalidInputError,
    LimitExceededError,
    NotEqualError,
)
from .proof import InvalidProofError, verify_proof

__all__ = [
    "CongruenceClosure",
    "verify_proof",
    "CongruenceClosureError",
    "InvalidInputError",
    "LimitExceededError",
    "BudgetExhaustedError",
    "NotEqualError",
    "ConflictError",
    "InvalidProofError",
    "DEFAULT_MAX_TERMS",
    "DEFAULT_WORK_BUDGET",
]

__version__ = "1.0.0"
