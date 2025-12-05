# run_all_tests.py

from ufrf_monster.modular_tests import test_modular_invariance, test_Z_equals_j_minus_744
from ufrf_monster.concurrency_sim import simulate_concurrency, analyze_concurrency

def main():
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
        print(f"τ={tau}: |Z(τ+1)-Z(τ)|={diff_T:.3e}, |Z(-1/τ)-Z(τ)|={diff_S:.3e}")

    print("\n=== Z(τ) vs j(τ)-744 numerical test ===")
    results_eq = test_Z_equals_j_minus_744(taus, N=10)
    for tau, diff in results_eq:
        print(f"τ={tau}: |Z(τ) - (j(τ)-744)|={diff:.3e}")

    print("\n=== Concurrency simulation (example) ===")
    periods = [13, 17, 19]
    actives = [{0, 5}, {3}, {7, 11}]
    L, flags = simulate_concurrency(periods, actives, T=500)
    max_gap, periodic = analyze_concurrency(L, flags)
    print(f"Periods={periods}, lcm L={L}")
    print(f"Max inactive run: {max_gap}, approx L-periodic={periodic}")

if __name__ == "__main__":
    main()

