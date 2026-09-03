import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_laurentBaseChange_gamma0_le_fieldBar

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.laurentBaseChange_gamma0_le_fieldBar (q M' : ℕ) :
    ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) ≤
      ModularCurve.FullLevel.fieldBar q M' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_laurentBaseChange_gamma0_le_fieldBar.solution
