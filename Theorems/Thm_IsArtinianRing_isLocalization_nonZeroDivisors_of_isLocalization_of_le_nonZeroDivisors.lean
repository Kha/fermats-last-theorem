import Mathlib
import P2M.Util
import P2M.Sol.S_IsArtinianRing_isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors

set_option autoImplicit false

theorem IsArtinianRing.isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors
    {B F : Type*} [CommRing B] [CommRing F] [Algebra B F]
    (M : Submonoid B) (hM : M ≤ nonZeroDivisors B) [IsLocalization M F] [IsArtinianRing F] :
    IsLocalization (nonZeroDivisors B) F := by p2m_exact_reverting @_root_.P2MW.S_IsArtinianRing_isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors.solution
