import Definitions.Def_LanglandsTunnell_HonestLDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_MellinUniqueness_eq_of_forall_continuous_char_exists_laplace_eq

set_option autoImplicit false
open MeasureTheory

theorem LanglandsTunnell.Converse.MellinUniqueness.eq_of_forall_continuous_char_exists_laplace_eq
    (C : Type) [Group C] [TopologicalSpace C] [CompactSpace C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure]
    (hsep : ∀ x : C, x ≠ 1 → ∃ χ : C →* ℂˣ, Continuous χ ∧ χ x ≠ 1)
    (f₁ f₂ : C × ℝ → ℂ) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (Λ : (C →* ℂˣ) → ℂ → ℂ)
    (hΛ : ∀ χ : C →* ℂˣ, Continuous χ → Differentiable ℂ (Λ χ))
    (hb : ∀ χ : C →* ℂˣ, Continuous χ → LDatum.BoundedOnStrips (Λ χ))
    (h : ∀ χ : C →* ℂˣ, Continuous χ → ∃ c : ℝ,
      (∀ s : ℂ, c < s.re →
        Integrable (fun p : C × ℝ => f₁ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ))) (μ.prod volume) ∧
          ∫ p : C × ℝ, f₁ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ s) ∧
      (∀ s : ℂ, s.re < -c →
        Integrable (fun p : C × ℝ => f₂ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ))) (μ.prod volume) ∧
          ∫ p : C × ℝ, f₂ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ s)) :
    f₁ = f₂ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_MellinUniqueness_eq_of_forall_continuous_char_exists_laplace_eq.solution
