import Mathlib
import P2M.Util
import P2M.Sol.S_ZSpan_norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt

set_option autoImplicit false

open MeasureTheory

theorem ZSpan.norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b : Module.Basis ι ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (ℓ : E →L[ℝ] ℝ) (v : E) (hv : ℓ v ≠ 0)
    (Hs : ℕ → E → ℂ) (hcont : ∀ j, Continuous (Hs j))
    (hderiv : ∀ (j : ℕ) (x : E), HasDerivAt (fun t : ℝ => Hs j (x + t • v)) (Hs (j + 1) x) 0)
    (hper : ∀ (j : ℕ) (x : E) (i : ι),
      Complex.exp (2 * Real.pi * Complex.I * ℓ (x + b i)) * Hs j (x + b i) =
        Complex.exp (2 * Real.pi * Complex.I * ℓ x) * Hs j x)
    (M : ℕ) :
    ‖∫ x in ZSpan.fundamentalDomain b, Complex.exp (2 * Real.pi * Complex.I * ℓ x) * Hs 0 x ∂μ‖ ≤
      ((2 * Real.pi * |ℓ v|)⁻¹) ^ M * ∫ x in ZSpan.fundamentalDomain b, ‖Hs M x‖ ∂μ := by p2m_exact_reverting @_root_.P2MW.S_ZSpan_norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt.solution
