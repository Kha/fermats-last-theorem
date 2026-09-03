import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
    (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ModularCurve.qExpFunctionFieldC K Γ =
      IntermediateField.adjoin K
        (⇑(ModularCurve.coeffMap (algebraMap k K)) '' (ModularCurve.qExpFunctionFieldC k Γ : Set (LaurentSeries k))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC.solution
