import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_HonestLDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :
    (∀ (s : ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      rsGlobalIntegral D s φ Θ =
        rsGlobalIntegral (transposeInvN (Fin 2) ⁻¹' D) (1 - s)
          (fun g => φ (transposeInvN (Fin 2) g)) (dualForm Θ)) ∧
    (IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
        (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) →
      IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range (transposeInvN (Fin 2) ⁻¹' D)
        (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.solution
