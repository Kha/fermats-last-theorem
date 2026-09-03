import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
namespace P2MW.S_groupCohomology_Kummer_kummerCocycle_mul_of_mem_fixingSubgroup

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) {p : ℕ}
    (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K) {a : K} {α : Ωˣ} (hα : algebraMap K Ω a = (α : Ω) ^ p)
    {σ τ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) (hτ : τ ∈ K.fixingSubgroup) :
    kummerCocycle α (σ * τ) = kummerCocycle α σ * kummerCocycle α τ := by

  rw [isMulCocycle₁_kummerCocycle α σ τ, mul_comm]
  congr 1
  have hp1 : ((kummerCocycle α τ : Ωˣ) : Ω) ^ p = 1 := by

    rw [kummerCocycle_apply, Units.val_div_eq_div_val, val_smul_units, div_pow, ← map_pow,
      ← hα]
    have : τ (algebraMap K Ω a) = algebraMap K Ω a :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ _ (a.2)
    rw [this, div_self]
    rw [hα]; exact pow_ne_zero _ α.ne_zero
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (hμ _ hp1)
  exact Units.ext (by rw [val_smul_units, hfix])
