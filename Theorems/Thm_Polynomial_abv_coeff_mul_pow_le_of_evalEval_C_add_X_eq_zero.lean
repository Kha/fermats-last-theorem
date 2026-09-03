import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero

set_option autoImplicit false

open Polynomial

theorem Polynomial.abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (G : Polynomial (Polynomial K)) (hG : ∀ i j, μ ((G.coeff i).coeff j) ≤ 1)
    (z₀ y₀ : K) (hz : μ z₀ ≤ 1) (hy : μ y₀ ≤ 1)
    (hsep : (Polynomial.derivative G).evalEval z₀ y₀ ≠ 0)
    (Y : PowerSeries K) (hY0 : PowerSeries.constantCoeff Y = y₀)
    (hY : (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
        (PowerSeries.C z₀ + PowerSeries.X) Y = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    μ (PowerSeries.coeff n Y) * μ ((Polynomial.derivative G).evalEval z₀ y₀) ^ (2 * n)
      ≤ μ ((Polynomial.derivative G).evalEval z₀ y₀) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero.solution
