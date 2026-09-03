import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem LanglandsTunnell.CubicInduction.box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hWc : Continuous W) (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (_hfin : (∑' α : ℚˣ, ∫⁻ x : AdeleRing (𝓞 ℚ) ℚ,
        (‖dualWhittakerFn3 W (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
            lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))‖₊ : ENNReal)
          ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) < ⊤) :
    ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
      (∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
          (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
            (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * (iotaGL (diagUnitGL2 a) * g))))) * ψ (-y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
    ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) *
      ∑' α : ℚˣ, ∫ x : AdeleRing (𝓞 ℚ) ℚ,
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
          lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))
        ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual.solution
