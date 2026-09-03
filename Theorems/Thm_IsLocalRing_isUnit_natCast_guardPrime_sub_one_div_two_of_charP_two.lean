import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isUnit_natCast_guardPrime_sub_one_div_two_of_charP_two

set_option autoImplicit false

theorem IsLocalRing.isUnit_natCast_guardPrime_sub_one_div_two_of_charP_two
    (R : Type*) [CommRing R] [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) 2]
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) :
    IsUnit (((ℓg - 1) / 2 : ℕ) : R) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isUnit_natCast_guardPrime_sub_one_div_two_of_charP_two.solution
