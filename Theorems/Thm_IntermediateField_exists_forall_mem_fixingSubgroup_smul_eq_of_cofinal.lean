import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal

set_option autoImplicit false

universe u v

open IntermediateField
theorem IntermediateField.exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hcof : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (x : Ωˣ) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ • x = x := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal.solution
