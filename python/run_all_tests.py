# run_all_tests.py
"""
Integration test runner for UFRF-Monster Moonshine validation.

Author: Daniel Charboneau
"""

from ufrf_monster.modular_tests import test_modular_invariance, test_Z_equals_j_minus_744
from ufrf_monster.concurrency_sim import simulate_concurrency, analyze_concurrency
from ufrf_monster.constants import B2, MONSTER_PRIMES, BREATHING_PERIOD, J1, J2, MONSTER_DIMENSION

def main():
    # Print geometric constants
    print("=== UFRF-Monster Geometric Constants ===")
    print(f"B2 = {B2:.10f}")
    print(f"B2 = (47 × 59 × 71 + 1) × {BREATHING_PERIOD}² / ({J1} × 60)")
    print(f"Monster primes: {MONSTER_PRIMES}")
    print(f"Monster dimension: {MONSTER_DIMENSION}")
    print(f"Verification: {MONSTER_PRIMES['p6']} × {MONSTER_PRIMES['p7']} × {MONSTER_PRIMES['p8']} + 1 = {MONSTER_DIMENSION}")
    print(f"B2 verification: {MONSTER_DIMENSION} × {BREATHING_PERIOD}² / ({J1} × 60) = {B2:.10f}")
    print()

    # Example τ values in the upper half-plane
    taus = [
        0.2 + 1.3j,
        0.1 + 0.9j,
        -0.3 + 1.7j,
        0.3 + 2.0j,
    ]

    print("=== Modular invariance numerical test ===")
    results_mod = test_modular_invariance(taus, N=10)
    for tau, diff_T, diff_S in results_mod:
        # Convert mpmath types to float for formatting
        diff_T_val = float(diff_T) if hasattr(diff_T, '__float__') else diff_T
        diff_S_val = float(diff_S) if hasattr(diff_S, '__float__') else diff_S
        print(f"τ={tau}: |Z(τ+1)-Z(τ)|={diff_T_val:.3e}, |Z(-1/τ)-Z(τ)|={diff_S_val:.3e}")

    print("\n=== Z(τ) vs j(τ)-744 numerical test ===")
    results_eq = test_Z_equals_j_minus_744(taus, N=10)
    for tau, diff in results_eq:
        diff_val = float(diff) if hasattr(diff, '__float__') else diff
        print(f"τ={tau}: |Z(τ) - (j(τ)-744)|={diff_val:.3e}")

    print("\n=== Concurrency simulation (example) ===")
    periods = [13, 17, 19]
    actives = [{0, 5}, {3}, {7, 11}]
    L, flags = simulate_concurrency(periods, actives, T=500)
    max_gap, periodic = analyze_concurrency(L, flags)
    print(f"Periods={periods}, lcm L={L}")
    print(f"Max inactive run: {max_gap}, approx L-periodic={periodic}")

if __name__ == "__main__":
    main()
