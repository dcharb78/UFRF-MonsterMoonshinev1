# concurrency_sim.py
"""
Multi-scale concurrency simulation and bounded-gap analysis.

Author: Daniel Charboneau
"""

from typing import List, Set, Tuple
from math import gcd
from functools import reduce

def lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)

def lcm_list(lst: List[int]) -> int:
    return reduce(lcm, lst)

def simulate_concurrency(
    periods: List[int],
    actives: List[Set[int]],
    T: int = 1000
) -> Tuple[int, List[bool]]:
    """
    Simulate concurrency for given periods and active residues.

    Returns:
      L: lcm of periods
      active_flags: list of booleans [Active(t)] for t in [0..T-1]
    """
    L = lcm_list(periods)
    active_flags = []
    for t in range(T):
        is_active = any((t % p) in A for p, A in zip(periods, actives))
        active_flags.append(is_active)
    return L, active_flags

def analyze_concurrency(L: int, active_flags: List[bool]) -> Tuple[int, bool]:
    """
    Given L and the time series of Active(t),
    compute:
      - max_inactive_run
      - periodicity_approx: whether pattern appears L-periodic in window
    """
    max_run = 0
    current_run = 0
    for flag in active_flags:
        if flag:
            current_run = 0
        else:
            current_run += 1
            if current_run > max_run:
                max_run = current_run
    # Periodicity check over first 2L steps if available
    periodic = False
    if len(active_flags) >= 2 * L:
        periodic = (active_flags[:L] == active_flags[L:2*L])
    return max_run, periodic

