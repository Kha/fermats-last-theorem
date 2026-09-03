import Definitions.Def_LanglandsTunnell_JLData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_isJLTwist

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem LanglandsTunnell.Converse.exists_isJLTwist (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (m : ↥S → ℕ)
    (hlevel : ∀ (v : ↥S) (u : (v.1.adicCompletion K)ˣ), Valued.v (u : v.1.adicCompletion K) = 1 →
      IsOneMod K v.1 (m v) u → epsS v.1 u = 1) :
    ∃ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsJLTwist K S epsS μ ∧
      ∀ v ∉ S, NumberField.TateGlobal.IsUnramifiedCharAt μ v := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_isJLTwist.solution
