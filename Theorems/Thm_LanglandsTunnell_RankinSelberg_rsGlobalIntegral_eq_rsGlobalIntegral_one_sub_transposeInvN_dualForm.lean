import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_HonestLDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_one_sub_transposeInvN_dualForm

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.rsGlobalIntegral_eq_rsGlobalIntegral_one_sub_transposeInvN_dualForm
    (D D' : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (hD' : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D'
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hΘ : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Θ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Θ g)
    (s : ℂ) :
    rsGlobalIntegral D s φ Θ =
      rsGlobalIntegral D' (1 - s) (fun g => φ (transposeInvN (Fin 2) g)) (dualForm Θ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_one_sub_transposeInvN_dualForm.solution
