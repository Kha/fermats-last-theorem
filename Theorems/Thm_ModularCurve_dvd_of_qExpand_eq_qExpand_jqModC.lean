import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularCurve_dvd_of_qExpand_eq_qExpand_jqModC

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.dvd_of_qExpand_eq_qExpand_jqModC
    (K : Type*) [Field K] (d N : ℕ) [NeZero d] [NeZero N] (y : LaurentSeries K)
    (h : ModularCurve.qExpand K d y = ModularCurve.qExpand K N (ModularCurve.jqModC K)) : d ∣ N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_dvd_of_qExpand_eq_qExpand_jqModC.solution
