import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn

set_option autoImplicit false

theorem ValuationSubring.isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (F : Type) [Field F] [Algebra F (AlgebraicClosure ℚ)] :
    IsAlgClosed (IsLocalRing.ResidueField
      ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ)))) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn.solution
