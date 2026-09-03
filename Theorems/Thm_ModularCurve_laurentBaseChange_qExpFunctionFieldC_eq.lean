import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq

set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve

theorem ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq
    (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ)) :
    ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ) = ModularCurve.qExpFunctionFieldC L Γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq.solution
