import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_setLIntegral_eq_setLIntegral_tsum_mirabolicRep

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open LanglandsTunnell.CubicInduction

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.CubicInduction.setLIntegral_eq_setLIntegral_tsum_mirabolicRep
    (DΓ DN : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hDΓ : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range DΓ (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (hDN : IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range DN
      (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)) :
    ∀ h : AdelicGL2 (𝓞 ℚ) ℚ → ENNReal, Measurable h →
      (∀ (x : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), h (globalPoints (𝓞 ℚ) ℚ (unipotentGL2 x) * g) = h g) →
      ∫⁻ g in DN, h g ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
        ∫⁻ g in DΓ, ∑' i : MirabolicIndex ℚ, h (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) * g)
          ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_setLIntegral_eq_setLIntegral_tsum_mirabolicRep.solution
