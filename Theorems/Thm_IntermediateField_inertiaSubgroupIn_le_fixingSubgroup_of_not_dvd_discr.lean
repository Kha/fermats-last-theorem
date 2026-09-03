import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_IntermediateField_inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr

theorem IntermediateField.inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F]
    (q : ℕ) (hq : q.Prime)
    (hdisc : haveI : NumberField F := @NumberField.mk _ _ inferInstance ‹FiniteDimensional ℚ F›;
             ¬ (q : ℤ) ∣ NumberField.discr F)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q) :
    P.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr.solution
