import Mathlib
import Theorems.Thm_IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral
import P2M.Util
namespace P2MW.S_IsLocalRing_isUnit_of_isUnit_mod_maximalIdeal_of_isIntegral

open IsLocalRing

theorem solution {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Algebra.IsIntegral R S] {a : S}
    (h : IsUnit ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S))) a)) :
    IsUnit a := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp h
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at hb
  exact isUnit_of_mul_isUnit_left <|
    Ideal.isUnit_of_sub_one_mem_jacobson_bot (a * b)
      (IsLocalRing.map_maximalIdeal_le_jacobson_bot_of_isIntegral hb)
