import Mathlib
import P2M.Util
import P2M.Sol.S_MellinParseval_integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le

set_option autoImplicit false

open MeasureTheory

theorem MellinParseval.integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le
    (σ σ₀ : ℝ) (_hσ₀ : 0 < σ₀) (f : ℂ → ℂ) (m : ℝ → ℝ)
    (_hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (_hm : Integrable m)
    (_hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t) :
    IntegrableOn (fun y : ℝ => ((y ^ (-σ) / y : ℝ) : ℂ) *
        ∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) * f ((σ : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi 0) := by p2m_exact_reverting @_root_.P2MW.S_MellinParseval_integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le.solution
