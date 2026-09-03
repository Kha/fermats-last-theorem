import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_IntermediateField_not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup

theorem IntermediateField.not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (q : ℕ) (hq : q.Prime)
    (hunr : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      P.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup) :
    haveI : NumberField F := @NumberField.mk _ _ inferInstance ‹FiniteDimensional ℚ F›
    ¬ (q : ℤ) ∣ NumberField.discr F := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup.solution
