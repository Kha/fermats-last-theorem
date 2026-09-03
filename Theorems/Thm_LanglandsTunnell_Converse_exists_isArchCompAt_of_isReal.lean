import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_isArchCompAt_of_isReal

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal

theorem LanglandsTunnell.Converse.exists_isArchCompAt_of_isReal (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ) (w : InfinitePlace K) (hw : w.IsReal) :
    ∃ u : ℂ, ∃ a : ZMod 2, IsArchCompAt K μ w u ((a.val : ℕ) : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_isArchCompAt_of_isReal.solution
