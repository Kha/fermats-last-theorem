import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_LanglandsTunnell_DeltaLift
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable
attribute [-instance] M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm LanglandsTunnell RSCarrier

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option autoImplicit false

theorem LanglandsTunnell.Converse.integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable

    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)] :

    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀

    (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
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
    (WArch FArch : GL (Fin 2) ℝ → ℂ) (Wf Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
    (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hf : ∀ g, f g =
      ((WArch (ratArchGL2 g) * FArch (ratArchGL2 g)) *
          (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
        ((Wf (finFactor g) * Ff (finFactor g)) *
          ((TateGlobal.ideleNorm ℚ
              (Matrix.GeneralLinearGroup.det (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2))))

    (_hfm : Measurable f)
    (_hinv : ∀ (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), f ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) = f g)
    (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ) (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q)

    (_hIq : Integrable (fun q : UnipotentQuotient ℚ => f (σq q)) (unipotentQuotientMeasure ℚ)),
    ∫ q, f (σq q) ∂(unipotentQuotientMeasure ℚ) =
      rsArchIntegral archMeasure μNArch s WArch FArch * rsFinIntegral μf μNFin s Wf Ff := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable.solution
