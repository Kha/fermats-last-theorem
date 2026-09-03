import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_deg_eq_one_modularFunctionFieldC
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel

open AlgebraicCurve ModularCurve
theorem P2M.Dup.ModularCurve.deg_eq_one_modularFunctionFieldC
    (K : Type*) [Field K] (N : ℕ) [NeZero N] [IsAlgClosed K]
    [IsCurveOver K (modularFunctionFieldC K N)] :
    ∀ w : Place K (modularFunctionFieldC K N), w.deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_deg_eq_one_modularFunctionFieldC.solution
#p2m_type_eq_warn P2M.Dup.ModularCurve.deg_eq_one_modularFunctionFieldC ModularCurve.deg_eq_one_modularFunctionFieldC
