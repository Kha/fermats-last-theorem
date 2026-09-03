import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c : ℕ) (hc : 2 ≤ c) :
    ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
      Continuous χ ∧ χ (uniformizerUnit K v) = 1 ∧ HasConductorExponentAt K v χ c := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt.solution
