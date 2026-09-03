import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt_apply_ne

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt_apply_ne
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (u₀ : (v.adicCompletion K)ˣ) (hu : Valued.v (u₀ : v.adicCompletion K) = 1) (hu₀ : u₀ ≠ 1)
    (z : ℂˣ) (d : ℕ) :
    ∃ c : ℕ, d ≤ c ∧ 2 ≤ c ∧ ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
      Continuous χ ∧ χ (uniformizerUnit K v) = 1 ∧ HasConductorExponentAt K v χ c ∧ χ u₀ ≠ z := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt_apply_ne.solution
