import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_sPartDual_eq_single

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.Converse.sPartDual_eq_single (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (n₀ : ↥S → ℤ)
    (hAd : ∀ n : ↥S → ℤ, n ≠ n₀ → Ad n = 0) :
    sPartDual K S Ad μ s = Ad n₀ * ∏ v : ↥S,
      ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n₀ v) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_sPartDual_eq_single.solution
