import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
namespace P2MW.S_groupCohomology_Kummer_kummerCocycle_mul_eq_of_apply_eq

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (α : Lˣ) (σ τ : L ≃ₐ[K] L) (hτ : τ (α : L) = α) :
    kummerCocycle α (σ * τ) = kummerCocycle α σ := by
  have hτ' : τ • α = α := Units.ext (by rw [val_smul_units, hτ])
  rw [kummerCocycle_apply, kummerCocycle_apply, mul_smul, hτ']
