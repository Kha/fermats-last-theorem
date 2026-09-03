import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_cofinal_comp_fixingSubgroupEquiv_symm

set_option autoImplicit false
theorem IntermediateField.cofinal_comp_fixingSubgroupEquiv_symm
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup) :
    (∀ E : IntermediateField L Ω, FiniteDimensional L E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ τ : Ω ≃ₐ[L] Ω,
          (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom)) τ
            ∈ F.fixingSubgroup → τ ∈ E.fixingSubgroup) ∧
    (∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField L Ω, FiniteDimensional L E ∧
        ∀ τ : Ω ≃ₐ[L] Ω, τ ∈ E.fixingSubgroup →
          (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom)) τ
            ∈ F.fixingSubgroup) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_cofinal_comp_fixingSubgroupEquiv_symm.solution
