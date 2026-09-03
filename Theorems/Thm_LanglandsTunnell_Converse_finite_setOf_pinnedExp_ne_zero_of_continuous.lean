import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_finite_setOf_pinnedExp_ne_zero_of_continuous

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem LanglandsTunnell.Converse.finite_setOf_pinnedExp_ne_zero_of_continuous
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ) :
    {v : HeightOneSpectrum (𝓞 K) | pinnedExp K μ v ≠ 0}.Finite := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_finite_setOf_pinnedExp_ne_zero_of_continuous.solution
