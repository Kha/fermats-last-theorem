import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_eval_int_eq_zero
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

open PowerSeries HahnSeries IntermediateField
theorem P2M.Dup.ModularCurve.ModularPolynomialData.eval_int_eq_zero {N : ℕ} [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) :
    data.Φ.eval₂ ModularCurve.evalAtJInt (ModularCurve.jqIntN N) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_eval_int_eq_zero.solution
#p2m_type_eq_warn P2M.Dup.ModularCurve.ModularPolynomialData.eval_int_eq_zero ModularCurve.ModularPolynomialData.eval_int_eq_zero
