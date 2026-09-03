import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_LanglandsTunnell_HonestLDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel
open NumberField.AdelicHaar NumberField.AdelicLevel LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded
    (F : Type) [Field F] [NumberField F]
    (c u : ℝ) (hc : 0 < c) (tset : Finset (AdelicGL2 (𝓞 F) F))
    (𝓕 : Set (AdelicGL2 (𝓞 F) F)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕μ : adelicGLHaar (Fin 2) (𝓞 F) F 𝓕 < ⊤)
    (h𝓕S : 𝓕 ⊆ ⋃ t ∈ tset, (· * t) '' integralWindowedSiegelSet F c u)
    (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφ'c : Continuous φ')
    (hφ : IsRapidlyDecreasingOnSiegelSets F φ) (hφ' : IsRapidlyDecreasingOnSiegelSets F φ')
    (H : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hHd : ∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => H s g))
    (hHc : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2)
    (hHb : IsUniformlySiegelBounded F H) :
    (∀ s : ℂ, IntegrableOn (fun g => φ g * φ' g * H s g) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
    Differentiable ℂ (fun s : ℂ => rs22GlobalIntegral F 𝓕 φ φ' (H s)) ∧
    LanglandsTunnell.LDatum.BoundedOnStrips (fun s : ℂ => rs22GlobalIntegral F 𝓕 φ φ' (H s)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded.solution
