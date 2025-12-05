# b2_sanity_check.py
"""
Numerical sanity-check for the B2 enhancement in the UFRF–Monster project.

Author: Daniel Charboneau
"""

from math import isclose

# B2 definition (must match your Lean definition)
B2 = 196884 * 169 / (744 * 60)

def main():
    print("Numeric sanity-check for B2")
    print("-" * 50)
    print(f"B2 value: {B2:.12f}")

    # Harmonic formula for j2:
    # j2 = 744 * (15/13) * (4/13) * B2
    factor = 744 * (15/13) * (4/13)
    j2_from_formula = factor * B2

    print(f"j2 from harmonic formula: {j2_from_formula:.12f}")
    print(f"expected j2 (Monster dimension): 196884")
    print(f"difference (j2_calc - 196884): {j2_from_formula - 196884:.12e}")

    # Check closeness
    ok = isclose(j2_from_formula, 196884, rel_tol=1e-10, abs_tol=1e-8)
    print(f"isclose(j2_calc, 196884)? {ok}")

if __name__ == '__main__':
    main()
