import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import P2M.Util
import P2M.Sol.S_ModularCurve_lambdaEval_kroneckerRemainder
set_option autoImplicit false

open ModularCurve ModularCurve.LambdaNodeLocalized

theorem ModularCurve.lambdaEval_kroneckerRemainder
    {q : ℕ} [Fact q.Prime] (data : LambdaModularPolynomialData q) (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
      + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    {L : Type*} [Field L] [Algebra ℚ L] (A : Subring L) :
    lambdaEval q A
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom A)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) A)
      = (algebraMap L (LaurentSeries L) (q : L))⁻¹
        * ((lambdaNModC L q - lambdaModC L ^ q) * (lambdaModC L - lambdaNModC L q ^ q)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_lambdaEval_kroneckerRemainder.solution
