import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_kummerCocycle_mul_eq_of_mem_fixingSubgroup_adjoin

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.kummerCocycle_mul_eq_of_mem_fixingSubgroup_adjoin
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (α : Lˣ) (σ τ : L ≃ₐ[K] L) (hτ : τ ∈ (IntermediateField.adjoin K {(α : L)}).fixingSubgroup) :
    kummerCocycle α (σ * τ) = kummerCocycle α σ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_kummerCocycle_mul_eq_of_mem_fixingSubgroup_adjoin.solution
