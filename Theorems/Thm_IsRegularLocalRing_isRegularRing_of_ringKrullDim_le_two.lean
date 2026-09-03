import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_isRegularRing_of_ringKrullDim_le_two

set_option autoImplicit false

theorem IsRegularLocalRing.isRegularRing_of_ringKrullDim_le_two
    (R : Type) [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2) :
    IsRegularRing R := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_isRegularRing_of_ringKrullDim_le_two.solution
