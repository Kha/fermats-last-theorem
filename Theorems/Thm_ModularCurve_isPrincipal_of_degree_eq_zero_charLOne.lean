import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero
import P2M.Util
import P2M.Sol.S_ModularCurve_isPrincipal_of_degree_eq_zero_charLOne
open AlgebraicCurve ModularCurve
theorem ModularCurve.isPrincipal_of_degree_eq_zero_charLOne {k : Type*} [Field k] (D : Divisor k (modularFunctionFieldC k 1)) (hD : Divisor.degree D = 0) : D.IsPrincipal := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isPrincipal_of_degree_eq_zero_charLOne.solution
