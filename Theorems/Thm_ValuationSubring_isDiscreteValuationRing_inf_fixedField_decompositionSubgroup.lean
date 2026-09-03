import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_inf_fixedField_decompositionSubgroup
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ) :
    IsDiscreteValuationRing ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring) ∧
      Irreducible ((ℓ : ℕ) : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring)) ∧
      ∀ x : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring),
        A.valuation (x : AlgebraicClosure ℚ) < 1 → ¬ IsUnit x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup.solution
