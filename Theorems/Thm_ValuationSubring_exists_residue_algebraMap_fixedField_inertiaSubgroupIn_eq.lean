import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq

set_option autoImplicit false

theorem ValuationSubring.exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime] (hA : A.LiesOverPrime q)
    (x : IsLocalRing.ResidueField ↥A) :
    ∃ y : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))),
      (IsLocalRing.residue ↥A)
          ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
              (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), y.2⟩ = x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq.solution
