import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_isArchCompAt_of_isComplex

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal

theorem LanglandsTunnell.Converse.exists_isArchCompAt_of_isComplex (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ) (w : InfinitePlace K) (hw : w.IsComplex) :
    ∃ u : ℂ, ∃ k : ℤ, IsArchCompAt K μ w u k := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_isArchCompAt_of_isComplex.solution
