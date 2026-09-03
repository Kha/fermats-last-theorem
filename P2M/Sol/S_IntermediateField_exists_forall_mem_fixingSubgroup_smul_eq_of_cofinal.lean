import Mathlib
import Theorems.Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq
import P2M.Util
namespace P2MW.S_IntermediateField_exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal

set_option autoImplicit false

universe u v

open IntermediateField

theorem solution
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hcof : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (x : Ωˣ) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ • x = x := by
  obtain ⟨E, hE, h⟩ := exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq (K := K) x
  obtain ⟨F, hF, hFE⟩ := hcof E hE
  exact ⟨F, hF, fun σ hσ => h σ (hFE σ hσ)⟩
