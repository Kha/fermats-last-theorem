import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one

set_option autoImplicit false

open NumberField NumberField.StandardAddChar IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) :
    addCharLevel (psiLocal M w.1) = addCharLevel (psiLocal E v) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one.solution
