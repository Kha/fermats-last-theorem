import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_kummerCocycle_mul_eq_of_apply_eq
import P2M.Util
namespace P2MW.S_groupCohomology_Kummer_kummerCocycle_mul_eq_of_mem_fixingSubgroup_adjoin

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (α : Lˣ) (σ τ : L ≃ₐ[K] L) (hτ : τ ∈ (IntermediateField.adjoin K {(α : L)}).fixingSubgroup) :
    kummerCocycle α (σ * τ) = kummerCocycle α σ := by
  exact kummerCocycle_mul_eq_of_apply_eq α σ τ
    ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ _
      (IntermediateField.subset_adjoin K _ (Set.mem_singleton _)))
