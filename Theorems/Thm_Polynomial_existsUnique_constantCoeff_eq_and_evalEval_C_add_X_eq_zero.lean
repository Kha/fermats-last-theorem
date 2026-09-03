import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_existsUnique_constantCoeff_eq_and_evalEval_C_add_X_eq_zero

set_option autoImplicit false

open Polynomial

theorem Polynomial.existsUnique_constantCoeff_eq_and_evalEval_C_add_X_eq_zero
    {K : Type*} [Field K] (G : Polynomial (Polynomial K)) (z₀ y₀ : K)
    (h0 : G.evalEval z₀ y₀ = 0) (hsep : (Polynomial.derivative G).evalEval z₀ y₀ ≠ 0) :
    ∃! Y : PowerSeries K, PowerSeries.constantCoeff Y = y₀ ∧
      (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
        (PowerSeries.C z₀ + PowerSeries.X) Y = 0 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_existsUnique_constantCoeff_eq_and_evalEval_C_add_X_eq_zero.solution
