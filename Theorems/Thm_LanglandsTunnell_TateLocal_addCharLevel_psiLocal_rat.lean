import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat

set_option autoImplicit false

open NumberField NumberField.StandardAddChar IsDedekindDomain

theorem LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat
    (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    addCharLevel (psiLocal ℚ v) = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat.solution
