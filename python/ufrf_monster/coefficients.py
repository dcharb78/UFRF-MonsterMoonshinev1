# coefficients.py
"""
UFRF/Monster coefficient functions.

Author: Daniel Charboneau
"""

from typing import Dict

# Known j(q) coefficients for small n:
# j(q) = q^{-1} + 744 + 196884 q + 21493760 q^2 + 864299970 q^3 + ...
# So j(q) - 744 = q^{-1} + 196884 q + 21493760 q^2 + 864299970 q^3 + ...

_KNOWN_A: Dict[int, int] = {
    -1: 1,
     0: 0,
     1: 196884,
     2: 21493760,
     3: 864299970,
}

def a(n: int) -> int:
    """
    UFRF/Monster coefficient a_n.

    Returns the coefficient for the j-function q-series expansion.
    Unknown coefficients default to 0.
    """
    if n in _KNOWN_A:
        return _KNOWN_A[n]
    else:
        return 0

