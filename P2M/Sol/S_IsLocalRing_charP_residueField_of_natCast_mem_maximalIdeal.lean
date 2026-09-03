import Mathlib
import P2M.Util
namespace P2MW.S_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal

set_option autoImplicit false

theorem solution
    (A : Type*) [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    CharP (IsLocalRing.ResidueField A) p := by
  have h0 : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hAp
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h0
