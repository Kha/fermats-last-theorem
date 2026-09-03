import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (ϖ : F) (hϖP : algebraMap F (AlgebraicClosure ℚ) ϖ ∈ P)
    (hirr : Irreducible (⟨ϖ, hϖP⟩ : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ))))) :
    IsDiscreteValuationRing
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ))) ∧
      Irreducible ((⟨⟨algebraMap F (AlgebraicClosure ℚ) ϖ, IntermediateField.algebraMap_mem _ ϖ⟩, hϖP⟩ :
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ))))) ∧
      CharZero
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ))) ∧
      ∀ y : AlgebraicClosure ℚ, y ∈ P → (∀ σ ∈ P.inertiaSubgroupIn F, σ y = y) →
        ∃ x : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ))),
          ((x : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F))) : AlgebraicClosure ℚ) = y := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible.solution
