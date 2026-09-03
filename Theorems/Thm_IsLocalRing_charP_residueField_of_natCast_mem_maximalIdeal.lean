import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal

set_option autoImplicit false

theorem IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal
    (A : Type*) [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    CharP (IsLocalRing.ResidueField A) p := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal.solution
