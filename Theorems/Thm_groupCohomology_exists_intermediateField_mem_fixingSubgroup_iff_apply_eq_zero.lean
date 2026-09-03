import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero

set_option autoImplicit false
open CategoryTheory

open groupCohomology
theorem groupCohomology.exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (p : ℕ) [Fact p.Prime]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (χ : (Ω ≃ₐ[K] Ω) → ZMod p) (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ)
    (hχlc : IsLevelConstant₁ r χ) (hχ0 : ∃ σ, χ σ ≠ 0) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ IsGalois K E ∧ Module.finrank K E = p ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup ↔ χ σ = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero.solution
