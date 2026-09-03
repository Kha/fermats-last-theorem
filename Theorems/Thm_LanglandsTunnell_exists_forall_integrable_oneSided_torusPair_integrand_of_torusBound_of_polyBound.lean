import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
    (β : ℂ) (g : ℝ → ℂ) (hg : Measurable g) (Cg σg : ℝ) (hσg : 0 ≤ σg)
    (hgb : ∀ τ : ℝ, τ ≠ 0 → ‖g τ‖ ≤ Cg * (1 + |τ| ^ (-σg)))
    (B : ℝ → ℝ → ℝ → ℝ → ℂ) (hB : Measurable fun x : ℝ × ℝ × ℝ × ℝ => B x.1 x.2.1 x.2.2.1 x.2.2.2)
    (CB : ℝ) (N : ℕ)
    (hBb : ∀ p q r z : ℝ, ‖B p q r z‖ ≤ CB * (1 + |p|) ^ N * (1 + |q|) ^ N * (1 + |r|) ^ N * (1 + |z|) ^ N) :
    ∃ σ₀ : ℝ, ∀ α γ : ℂ, σ₀ < α.re → γ.re < -σ₀ →
      Integrable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ β * ((x.2.2.1 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2.1) *
          (B (x.2.1⁻¹) (x.2.2.1⁻¹) (x.1 * x.2.1) x.2.2.2 * (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod volume))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound.solution
