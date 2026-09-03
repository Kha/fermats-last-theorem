import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_ModularCurve_KroneckerTransport
import P2M.Util
import P2M.Sol.S_ModularCurve_laurentMap_evalAtLambdaInt_kroneckerRemainder_eval_X_pow
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.laurentMap_evalAtLambdaInt_kroneckerRemainder_eval_X_pow
    (q : ℕ) [Fact q.Prime] (data : LambdaModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    (S : LaurentSeries ℤ) (hS : qExpand ℤ q lambdaInt - lambdaInt ^ q = (q : LaurentSeries ℤ) * S)
    (k : Type*) [Field k] [CharP k q] :
    laurentMap (Int.castRingHom k) (evalAtLambdaInt (R.eval (Polynomial.X ^ q))) =
      - laurentMap (Int.castRingHom k) S * (lambdaModC k ^ (q ^ 2) - lambdaModC k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_laurentMap_evalAtLambdaInt_kroneckerRemainder_eval_X_pow.solution
