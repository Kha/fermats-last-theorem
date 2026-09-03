import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
    (P : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hP : P.LiesOverPrime ℓ) :
    IsDiscreteValuationRing
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ∧
      Irreducible ((ℓ : ℕ) :
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ∧
      CharZero
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ∧
      ∀ y : AlgebraicClosure ℚ, y ∈ P → (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ y = y) →
        ∃ x : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))),
          ((x : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ) = y := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn.solution
