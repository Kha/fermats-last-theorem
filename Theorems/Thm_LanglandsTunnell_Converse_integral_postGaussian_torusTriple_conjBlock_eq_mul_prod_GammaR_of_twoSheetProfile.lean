import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_integral_postGaussian_torusTriple_conjBlock_eq_mul_prod_GammaR_of_twoSheetProfile

set_option autoImplicit false

p2m_open "NumberField LanglandsTunnell~integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div~integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance LanglandsTunnell.Converse MeasureTheory"

theorem LanglandsTunnell.Converse.integral_postGaussian_torusTriple_conjBlock_eq_mul_prod_GammaR_of_twoSheetProfile
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2) (h12 : a₁ ≠ a₂)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (μ₁ μ₂ : ℂ) (c₁ c₂ : ZMod 2) (hc : c₁ ≠ c₂) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c₁ μ₂ c₂)
    (ρ : ℂ)
    (hρ : ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ : ZMod 2) (n : ℕ) (hn : n = 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      ∫ q : ℝ × ℝ × ℝ,
        (ArchR.quasiChar (u₀ + 2) a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
          (((|q.2.1 * q.2.2| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (q.2.2 : ℂ)) ^ n *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) * ((|q.2.1| : ℝ) : ℂ)) *
          (W q.1 * D.W (ArchR.diagOne (a * q.1 * q.2.1 / q.2.2)) * (((|q.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.1 ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * q.1) ^ 2 * q.2.1 ^ 2))) : ℂ) * (((1 / q.2.1 - 1 / q.2.2 - a * q.1 * q.2.1 : ℝ)) : ℂ))))
        ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) =
      (-1 : ℂ) ^ (a₀.val + 1) * ρ * (1 / 4 : ℂ) *
        ((Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + u₀) + signShift (a₁ + a₀))) *
          Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + u₀) + signShift (a₂ + a₀)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + μ₁) + signShift (a₁ + c₁))) *
            Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + μ₁) + signShift (a₂ + c₁)))) *
            (Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + μ₂) + signShift (a₁ + c₂))) *
              Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + μ₂) + signShift (a₂ + c₂)))))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_integral_postGaussian_torusTriple_conjBlock_eq_mul_prod_GammaR_of_twoSheetProfile.solution
