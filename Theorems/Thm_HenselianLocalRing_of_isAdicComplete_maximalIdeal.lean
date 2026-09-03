import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_of_isAdicComplete_maximalIdeal

set_option autoImplicit false

universe u
theorem HenselianLocalRing.of_isAdicComplete_maximalIdeal (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : HenselianLocalRing R := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_of_isAdicComplete_maximalIdeal.solution
