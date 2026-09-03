import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_jqModC_mem_intFormRatiosC

theorem ModularCurve.jqModC_mem_intFormRatiosC (K : Type*) [Field K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ModularCurve.jqModC K ∈ ModularCurve.intFormRatiosC K Γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqModC_mem_intFormRatiosC.solution
