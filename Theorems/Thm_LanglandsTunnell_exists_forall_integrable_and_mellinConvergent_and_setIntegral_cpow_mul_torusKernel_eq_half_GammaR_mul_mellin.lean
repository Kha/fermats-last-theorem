import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin
    (b : ℝ) (hb : 0 < b) (p : ℂ)
    (g : ℝ → ℂ) (hgm : Measurable g) (C σ : ℝ) (hσ : 0 ≤ σ)
    (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * (1 + t ^ (-σ)))
    (K : ℝ → ℂ) (hKm : Measurable K) (CK N : ℝ)
    (hK : ∀ w : ℝ, 0 < w → ‖K w‖ ≤ CK * (w ^ N + w ^ (-N)) * Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + b * w ^ 2))))
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * b * σ' ^ 2)) : ℂ) * ∫ w in Ioi (0 : ℝ), g (σ' / w) * K w) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
          ((q.1 : ℝ) : ℂ) ^ (s - 2) * (((q.2.1 : ℝ) : ℂ) ^ p * K q.2.2 *
            (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + b * q.1 ^ 2 * q.2.1 ^ 2))) : ℂ) * g (q.1 * q.2.1 / q.2.2)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) ∧
      MellinConvergent H (s - 1) ∧
      ∫ y in Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
          ∫ y₁ in Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((y₁ : ℝ) : ℂ) ^ p * K y₂ * (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + b * y ^ 2 * y₁ ^ 2))) : ℂ) * g (y * y₁ / y₂) =
        (1 / 2 : ℂ) * Complex.Gammaℝ (s - p - 2) * mellin H (s - 1) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin.solution
