import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.StandardAddChar
open scoped nonZeroDivisors

theorem LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    addCharLevel (psiLocal K v)
      = FractionalIdeal.count K v (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal.solution
