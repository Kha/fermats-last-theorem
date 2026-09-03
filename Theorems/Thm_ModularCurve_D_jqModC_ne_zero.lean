import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Differentials
import P2M.Util
import P2M.Sol.S_ModularCurve_D_jqModC_ne_zero
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

theorem ModularCurve.D_jqModC_ne_zero (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    KaehlerDifferential.D K (ModularCurve.modularFunctionFieldC K N)
      ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_D_jqModC_ne_zero.solution
