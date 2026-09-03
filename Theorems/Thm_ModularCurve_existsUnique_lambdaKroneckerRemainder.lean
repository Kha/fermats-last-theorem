import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_ModularCurve_KroneckerTransport
import P2M.Util
import P2M.Sol.S_ModularCurve_existsUnique_lambdaKroneckerRemainder
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.existsUnique_lambdaKroneckerRemainder (q : ℕ) [Fact q.Prime]
    (data : LambdaModularPolynomialData q) (hK : reduceModBivar q data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)) :
    ∃! R : Polynomial (Polynomial ℤ), data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_existsUnique_lambdaKroneckerRemainder.solution
