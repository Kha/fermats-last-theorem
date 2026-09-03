import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_sPart_shift

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.Converse.sPart_shift (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (A : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (m : ↥S → ℤ) :
    (∏ v : ↥S,
        (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v)) *
      sPart K S A μ s = sPart K S (fun n => A (n - m)) μ s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_sPart_shift.solution
