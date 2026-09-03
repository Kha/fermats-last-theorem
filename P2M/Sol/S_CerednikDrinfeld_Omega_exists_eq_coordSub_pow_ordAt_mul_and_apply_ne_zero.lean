import Mathlib
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Theorems.Thm_CerednikDrinfeld_Omega_bddAbove_setOf_coordSub_pow_dvd
import Theorems.Thm_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F : ↥(Omega.holRing ϖ)) (hF : F ≠ 0) (z : ↥(Omega.upperHalfPlane K₀ K)) :
    ∃ G : ↥(Omega.holRing ϖ),
      F = Omega.coordSub ϖ z ^ Omega.ordAt ϖ F z * G ∧ (G : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 := by
  have hb : BddAbove {n : ℕ | coordSub ϖ z ^ n ∣ F} :=
    bddAbove_setOf_coordSub_pow_dvd K₀ K hrk ϖ hex hfin F hF z
  have hmem : ordAt ϖ F z ∈ {n : ℕ | coordSub ϖ z ^ n ∣ F} := by
    rw [ordAt_def]
    exact Nat.sSup_mem ⟨0, zero_mem_setOf_pow_dvd ϖ F z⟩ hb
  obtain ⟨G, hG⟩ := (hmem : coordSub ϖ z ^ ordAt ϖ F z ∣ F)
  refine ⟨G, hG, fun hGz => ?_⟩

  obtain ⟨G', hG'⟩ := coordSub_dvd_of_apply_eq_zero K₀ K ϖ hrk hex G z hGz
  have hdvd : coordSub ϖ z ^ (ordAt ϖ F z + 1) ∣ F := ⟨G', by rw [pow_succ, mul_assoc, ← hG']; exact hG⟩
  have := le_ordAt_of_pow_dvd ϖ F z hdvd hb
  omega
