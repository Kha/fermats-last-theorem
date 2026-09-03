import Definitions.Def_LanglandsTunnell_JLData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_nonempty_sOrderReps

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem LanglandsTunnell.Converse.nonempty_sOrderReps (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Nonempty (SOrderReps K S) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_nonempty_sOrderReps.solution
