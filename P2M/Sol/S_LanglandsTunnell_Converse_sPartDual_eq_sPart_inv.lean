import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
namespace P2MW.S_LanglandsTunnell_Converse_sPartDual_eq_sPart_inv

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open LanglandsTunnell.Converse

theorem solution (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) :
    sPartDual K S Ad μ s = sPart K S Ad μ⁻¹ s := by
  simp only [sPart, sPartDual, MonoidHom.inv_apply]
