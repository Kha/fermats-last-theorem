import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero
import P2M.Util
namespace P2MW.S_ModularCurve_isPrincipal_of_degree_eq_zero_charLOne
open AlgebraicCurve ModularCurve

theorem solution {k : Type*} [Field k] (D : Divisor k (modularFunctionFieldC k 1))
    (hD : Divisor.degree D = 0) : D.IsPrincipal :=
  Pic0.forall_isPrincipal_of_ringEquiv (ratFuncEquivCharLOneC k).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC k).commutes a)
    (fun E hE => RationalFunctionField.isPrincipal_of_degree_eq_zero E hE) D hD
