import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_eq_zero_of_mellin_eq_GammaC_mul_of_sub_rpow_bound_near_zero

set_option autoImplicit false

open Real Complex Filter Topology MeasureTheory

theorem LanglandsTunnell.eq_zero_of_mellin_eq_GammaC_mul_of_sub_rpow_bound_near_zero
    (ν : ℝ) (hν : 0 ≤ ν) (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Ioi 0))
    (c a b : ℂ) (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hnear : ∀ y : ℝ, 0 < y → y ≤ 1 →
      (0 < ν → ‖f y - c * (y : ℂ) ^ ((1 / 2 - ν : ℝ) : ℂ)‖ ≤ C * y ^ (1 / 2 - ν + δ)) ∧
      (ν = 0 → ‖f y - (a + b * (Real.log y : ℂ)) * (Real.sqrt y : ℂ)‖ ≤ C * y ^ (1 / 2 + δ)))
    (σ₀ : ℝ) (Ψ : ℂ → ℂ) (hΨ : Differentiable ℂ Ψ)
    (hmel : ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent f s ∧ mellin f s = Complex.Gammaℂ (s + 1 / 2 + (ν : ℂ)) * Ψ s) :
    (0 < ν → c = 0) ∧ (ν = 0 → b = 0) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_eq_zero_of_mellin_eq_GammaC_mul_of_sub_rpow_bound_near_zero.solution
