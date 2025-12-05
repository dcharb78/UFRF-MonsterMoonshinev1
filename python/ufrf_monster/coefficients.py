# coefficients.py

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
     # add more if desired
}

def a(n: int) -> int:
    """
    UFRF/Monster coefficient a_n.

    For now, we hard-code the first few. Later, this function can
    be replaced to pull from Lean-generated data or an external table.
    """
    if n in _KNOWN_A:
        return _KNOWN_A[n]
    else:
        # Fallback: 0 or raise. For numerical tests it's fine to return 0
        # beyond a certain truncation.
        return 0

