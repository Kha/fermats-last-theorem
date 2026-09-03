import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup

set_option autoImplicit false

theorem ValuationSubring.henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ) :
    HenselianLocalRing ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring) ∧
      (∃ π : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring) →+* ZMod ℓ,
        Function.Surjective π ∧
        ∀ x : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring),
          π x = 0 ↔ A.valuation (x : AlgebraicClosure ℚ) < 1) ∧
      ∀ x : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring),
        ¬ IsUnit x ↔ A.valuation (x : AlgebraicClosure ℚ) < 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup.solution
