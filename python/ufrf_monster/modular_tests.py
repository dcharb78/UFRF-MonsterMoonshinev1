# modular_tests.py
"""
Modular invariance tests for Z(τ) and j(τ).

Author: Daniel Charboneau
"""

from typing import List, Tuple
from mpmath import mp
from .partition import Z_tau, j_tau_series

mp.dps = 50

def test_modular_invariance(
    taus: List[complex],
    N: int = 10
) -> List[Tuple[complex, float, float]]:
    """
    For each τ, compute:
      |Z(τ+1) - Z(τ)| and |Z(-1/τ) - Z(τ)|
    using truncation up to N terms.

    Returns a list of (τ, diff_T, diff_S).
    """
    results = []
    for tau in taus:
        Z = Z_tau(tau, N=N)
        Z_T = Z_tau(tau + 1, N=N)
        Z_S = Z_tau(-1 / tau, N=N)
        diff_T = abs(Z_T - Z)
        diff_S = abs(Z_S - Z)
        results.append((tau, diff_T, diff_S))
    return results

def test_Z_equals_j_minus_744(
    taus: List[complex],
    N: int = 10
) -> List[Tuple[complex, float]]:
    """
    For each τ, compute |Z(τ) - (j(τ) - 744)| with truncation up to N.
    """
    results = []
    for tau in taus:
        Z = Z_tau(tau, N=N)
        j_val = j_tau_series(tau, N=N)
        diff = abs(Z - (j_val - 744))
        results.append((tau, diff))
    return results

