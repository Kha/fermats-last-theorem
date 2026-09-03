import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
namespace P2MW.S_groupCohomology_Kummer_kummerCocycle_eq_of_pow_eq_of_mem_fixingSubgroup

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) {p : ℕ}
    (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K) {a : K} {α β : Ωˣ}
    (hα : algebraMap K Ω a = (α : Ω) ^ p) (hβ : algebraMap K Ω a = (β : Ω) ^ p)
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) :
    kummerCocycle α σ = kummerCocycle β σ := by
  have hq : (α / β) ^ p = 1 := by
    rw [div_pow, div_eq_one]
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hα, ← hβ]
  have hfix : σ • (α / β) = α / β :=
    Units.ext ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _
      (hμ _ (by rw [← Units.val_pow_eq_pow_val, hq, Units.val_one])))
  rw [← div_eq_one, kummerCocycle_apply, kummerCocycle_apply, div_div_div_comm, ← smul_units_div,
    hfix, div_self']
