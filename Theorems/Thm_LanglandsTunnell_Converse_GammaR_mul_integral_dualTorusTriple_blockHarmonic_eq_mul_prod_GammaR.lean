import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_blockHarmonic_eq_mul_prod_GammaR

set_option autoImplicit false

p2m_open "NumberField AutomorphicForm LanglandsTunnell~integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections~integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance LanglandsTunnell.Converse~exists_forall_integrable_dualQuadruple_and_torusTriple_blockHarmonic_of_mulConvGaussian_sheets MeasureTheory"

theorem LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_blockHarmonic_eq_mul_prod_GammaR
    (ν₁ ν₂ : ℂ) (a₁ a₂ c : ZMod 2) (h12 : a₁ ≠ a₂)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ sP : ZMod 2) (ha₀ : a₀ = c) (hsP : sP = a₁ + a₂) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + 1 + 1) *
        (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2 - (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      (-1 : ℂ) ^ c.val * ρ * ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (a₁ + c))) *
          Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (a₂ + c)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -μ₁) + signShift (a₁ + c))) *
            Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -μ₁) + signShift (a₂ + c)))) *
            (Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -μ₂) + signShift (a₁ + c))) *
              Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -μ₂) + signShift (a₂ + c)))))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_blockHarmonic_eq_mul_prod_GammaR.solution
