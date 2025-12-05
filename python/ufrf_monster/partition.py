# partition.py
"""
UFRF partition function Z(τ) and j-function q-series evaluation.

Author: Daniel Charboneau
"""

from typing import Union
from mpmath import mp
from .coefficients import a

Number = Union[float, complex]

def Z_tau(tau: Number, N: int = 10) -> complex:
    """
    Truncated UFRF partition function Z(τ) = sum_{n=-1}^N a_n q^n,
    where q = exp(2πi τ).

    N controls how many terms are used.
    """
    mp.dps = 50
    q = mp.e ** (2j * mp.pi * tau)
    total = mp.mpc(0)
    for n in range(-1, N + 1):
        total += a(n) * (q ** n)
    return total

def j_tau_series(tau: Number, N: int = 10) -> complex:
    """
    Truncated j(τ) via its q-expansion:

    j(q) = q^{-1} + 744 + 196884 q + 21493760 q^2 + 864299970 q^3 + ...

    Uses the same a_n but adds 744 back in.
    """
    mp.dps = 50
    q = mp.e ** (2j * mp.pi * tau)
    total = mp.mpc(0)
    total += 744  # constant term
    # q^{-1} term
    total += a(-1) * (q ** -1)
    for n in range(1, N + 1):
        total += a(n) * (q ** n)
    return total

