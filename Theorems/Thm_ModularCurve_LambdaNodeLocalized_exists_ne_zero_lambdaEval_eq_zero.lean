import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import P2M.Util
import P2M.Sol.S_ModularCurve_LambdaNodeLocalized_exists_ne_zero_lambdaEval_eq_zero
set_option autoImplicit false

open ModularCurve ModularCurve.LambdaNodeLocalized

theorem ModularCurve.LambdaNodeLocalized.exists_ne_zero_lambdaEval_eq_zero
    {q : ℕ} [Fact q.Prime] (data : LambdaModularPolynomialData q)
    {L : Type*} [Field L] [Algebra ℚ L] (A : Subring L) :
    ∃ P : MvPolynomial (Fin 2) A, P ≠ 0 ∧ lambdaEval q A P = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ne_zero_lambdaEval_eq_zero.solution
