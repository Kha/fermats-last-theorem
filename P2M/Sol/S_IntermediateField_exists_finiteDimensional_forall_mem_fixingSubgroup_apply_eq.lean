import Mathlib
import P2M.Util
namespace P2MW.S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq

set_option autoImplicit false

universe u v

open IntermediateField

theorem solution
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Ω) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ x = x := by
  exact
    ⟨IntermediateField.adjoin K {x},
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x),
      fun σ hσ => (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ x
        (IntermediateField.subset_adjoin K _ (Set.mem_singleton x))⟩
