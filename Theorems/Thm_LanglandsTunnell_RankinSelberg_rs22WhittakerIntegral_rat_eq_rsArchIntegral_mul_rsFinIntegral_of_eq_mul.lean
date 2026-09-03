import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_LanglandsTunnell_DeltaLift
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_rs22WhittakerIntegral_rat_eq_rsArchIntegral_mul_rsFinIntegral_of_eq_mul
attribute [-instance] M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier

theorem LanglandsTunnell.RankinSelberg.rs22WhittakerIntegral_rat_eq_rsArchIntegral_mul_rsFinIntegral_of_eq_mul
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)] :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
      (μNArch : Measure realUnipotent) [μNArch.IsHaarMeasure]
      (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure]
      (_hsplit : Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (LanglandsTunnell.ratArchGL2 g, RSCarrier.finFactor g))
          (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
          RSCarrier.archMeasure.prod μf)
      (_hNsplit : Measure.map
          (fun n : adelicUnipotent ℚ => (LanglandsTunnell.ratArchGL2 n, RSCarrier.finFactor n))
          (unipotentHaar ℚ) =
          (Measure.map Subtype.val μNArch).prod (Measure.map Subtype.val μNFin))
      (s : ℂ)
      (W W' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (WA WA' FA : GL (Fin 2) ℝ → ℂ) (Wf Wf' Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
      (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
      (_hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W g = WA (ratArchGL2 g) * Wf (finFactor g))
      (_hW' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' g = WA' (ratArchGL2 g) * Wf' (finFactor g))
      (_hΦ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Φ (bottomRowVec ℚ g 1) = FA (ratArchGL2 g) * Ff (finFactor g))
      (_hm : Measurable fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
          W g * W' g * rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ s g)
      (_hinv : ∀ (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          W ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) * W' ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) = W g * W' g)
      (_hint : Integrable (fun p : GL (Fin 2) ℝ × finiteAdelicGL2Subgroup ℚ =>
          ((WA p.1 * (WA' p.1 * FA p.1)) *
              (((|(Matrix.GeneralLinearGroup.det p.1 : ℝ)| : ℝ) : ℂ) ^ ((s + 1) - 1 / 2))) *
            ((Wf p.2 * (Wf' p.2 * Ff p.2)) *
              ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (p.2 : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ)
                ^ ((s + 1) - 1 / 2))))
        ((archMeasure.withDensity (HaarQuotient.density realUnipotent μNArch)).prod
          (μf.withDensity (HaarQuotient.density finUnipotent μNFin)))),
      rs22WhittakerIntegral ℚ W W' 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ s =
        rsArchIntegral archMeasure μNArch (s + 1) WA (fun h => WA' h * FA h) *
          rsFinIntegral μf μNFin (s + 1) Wf (fun h => Wf' h * Ff h) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_rs22WhittakerIntegral_rat_eq_rsArchIntegral_mul_rsFinIntegral_of_eq_mul.solution
