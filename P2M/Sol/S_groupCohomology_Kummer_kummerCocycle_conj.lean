import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
namespace P2MW.S_groupCohomology_Kummer_kummerCocycle_conj

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (α : Ωˣ) (g σ : Ω ≃ₐ[k] Ω) :
    kummerCocycle (g • α) (g * σ * g⁻¹) = g • kummerCocycle α σ := by
  rw [kummerCocycle_apply, kummerCocycle_apply, smul_units_div, ← mul_smul, ← mul_smul,
    inv_mul_cancel_right]
