import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central

set_option autoImplicit false

open MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central
    {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
    [MeasurableSpace Kˣ] [MeasurableMul Kˣ] (μ : Measure Kˣ) [μ.IsMulLeftInvariant]
    (ψ : AddChar K ℂ) (W : GL (Fin 3) K → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (ω : Kˣ →* ℂˣ)
    (hω : ∀ (z : Kˣ) (g : GL (Fin 3) K), W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (χ₀ χ₁ : Kˣ →* ℂˣ) (s : ℂ) (u : Kˣ) :
    (∫ a : Kˣ, ∫ t : Kˣ,
        (((χ₁ a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : K) : ℝ) : ℂ) ^ s *
          (((χ₀ t : ℂˣ) : ℂ) * ((modulus (t : K) : ℝ) : ℂ) ^ (-s - 1))) *
        W (iotaGL (diagUnits2 (t * a) a) * (longWeyl3 * upperUnipotent3 0 0 (u : K) * weylPrime3)) ∂μ ∂μ) =
      ((χ₀ (-1) : ℂˣ) : ℂ) * ((χ₀ u : ℂˣ) : ℂ) * ((χ₁ u : ℂˣ) : ℂ)⁻¹ * (((modulus (u : K) : ℝ) : ℂ))⁻¹ *
      ∫ a : Kˣ, ∫ t : Kˣ,
        (((χ₁ a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : K) : ℝ) : ℂ) ^ s *
          (((χ₀ t : ℂˣ) : ℂ) * ((modulus (t : K) : ℝ) : ℂ) ^ (-s - 1))) *
        W (iotaGL (diagUnits2 (t * a) a) *
          (longWeyl3 * upperUnipotent3 0 0 ((u⁻¹ : Kˣ) : K) * longWeyl3 * weylPrime3)) ∂μ ∂μ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central.solution
