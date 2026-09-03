import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (c : HeightOneSpectrum (𝓞 ℚ) → ℕ) (hc : ∀ v ∈ S, 3 ≤ c v) :
    ∃ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ χ ∧
      (∀ v ∈ S, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar χ v) (c v)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → IsUnramifiedCharAt χ v) ∧
      ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ χ w 0 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le.solution
