# constants.py
"""
UFRF-Monster geometric constants.

Author: Daniel Charboneau

These constants are geometrically determined from UFRF first principles,
not empirically fitted. See Monster_Moonshine.lean for formal proofs.
"""

# B2 constant: geometrically derived from Monster primes (47, 59, 71)
# B2 = (47 × 59 × 71 + 1) × 13² / (744 × 60)
#    = 196884 × 169 / (744 × 60)
B2 = 196884 * 169 / (744 * 60)

# Monster primes at breathing positions
MONSTER_PRIMES = {
    'p6': 71,  # Position 6 mod 13
    'p7': 59,  # Position 7 mod 13
    'p8': 47,  # Position 8 mod 13
}

# Breathing period
BREATHING_PERIOD = 13

# j-function coefficients
J1 = 744
J2 = 196884

# Monster prime product
MONSTER_PRIME_PRODUCT = 47 * 59 * 71  # = 196883

# Unity completion
MONSTER_DIMENSION = MONSTER_PRIME_PRODUCT + 1  # = 196884

