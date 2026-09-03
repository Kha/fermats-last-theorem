import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import P2M.Util
import P2M.Sol.S_ModularCurve_frobenius_identity_lambda
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.frobenius_identity_lambda (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    lambdaNModC K ℓ = (lambdaModC K) ^ ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frobenius_identity_lambda.solution
