import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isUnit_natCast_guardPrime_sub_one_of_charP_three

set_option autoImplicit false

theorem IsLocalRing.isUnit_natCast_guardPrime_sub_one_of_charP_three
    (R : Type*) [CommRing R] [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) 3]
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) :
    IsUnit ((ℓg - 1 : ℕ) : R) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isUnit_natCast_guardPrime_sub_one_of_charP_three.solution
