import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_eval_mul_cpow_eq_mul_cpow_mul_eval_of_laurent_fe_of_rational_fe

set_option autoImplicit false

open Polynomial

theorem LanglandsTunnell.RankinSelberg.eval_mul_cpow_eq_mul_cpow_mul_eval_of_laurent_fe_of_rational_fe
    (N : ℕ) (hN : 1 < N) (Z Zd : ℂ → ℂ) (E : ℂ) (e : ℤ)
    (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ)
    (hZ : ∀ s : ℂ, σ₀ < s.re → Z s = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)))
    (hZd : ∀ s : ℂ, s.re < σ₁ → Zd s = (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)))
    (hE : ∀ s : ℂ, (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) =
      (E * (N : ℂ) ^ ((e : ℂ) * s)) * ((N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))))
    (P' Q' Pd' Qd' Γn Γd : Polynomial ℂ) (m' md' a : ℤ) (σ₀' σ₁' : ℝ) (hQ' : Q' ≠ 0) (hQd' : Qd' ≠ 0)
    (hZ' : ∀ s : ℂ, σ₀' < s.re → Z s * Q'.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s)))
    (hZd' : ∀ s : ℂ, s.re < σ₁' → Zd s * Qd'.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((md' : ℂ) * s) * Pd'.eval ((N : ℂ) ^ (-s)))
    (hΓ : ∀ s : ℂ, Γd.eval ((N : ℂ) ^ (-s)) * ((N : ℂ) ^ ((md' : ℂ) * s) * Pd'.eval ((N : ℂ) ^ (-s))) * Q'.eval ((N : ℂ) ^ (-s)) =
      Γn.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) * ((N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s))) * Qd'.eval ((N : ℂ) ^ (-s)))
    (hP : P ≠ 0) :
    ∀ s : ℂ, Γn.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) = E * (N : ℂ) ^ ((e : ℂ) * s) * Γd.eval ((N : ℂ) ^ (-s)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_eval_mul_cpow_eq_mul_cpow_mul_eval_of_laurent_fe_of_rational_fe.solution
