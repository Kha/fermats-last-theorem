import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_HonestLDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_differentiable_and_boundedOnStrips_rsGlobalIntegral_of_hasIotaMoments

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.differentiable_and_boundedOnStrips_rsGlobalIntegral_of_hasIotaMoments
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΘc : Continuous Θ) (hΘ : HasIotaMoments Θ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (C r : ℝ) (hφ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ ≤ C * detNorm g ^ r) :
    Differentiable ℂ (fun s : ℂ => rsGlobalIntegral D s φ Θ) ∧
      LanglandsTunnell.LDatum.BoundedOnStrips (fun s : ℂ => rsGlobalIntegral D s φ Θ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_differentiable_and_boundedOnStrips_rsGlobalIntegral_of_hasIotaMoments.solution
