import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne
set_option autoImplicit false

open Polynomial ModularCurve

theorem ModularCurve.derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne
    (ℓ : ℕ) [Fact ℓ.Prime] (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (b : k) (hb : b ^ (ℓ ^ 2) ≠ b) :
    (Polynomial.derivative (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval b (b ^ ℓ) ≠ 0 ∧
    (Polynomial.derivative ((swapBivar data.Φ).map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval b (b ^ ℓ) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne.solution
