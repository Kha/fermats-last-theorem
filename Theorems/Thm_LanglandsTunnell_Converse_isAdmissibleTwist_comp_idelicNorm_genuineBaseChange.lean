import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_isAdmissibleTwist_comp_idelicNorm_genuineBaseChange

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain LanglandsTunnell.Converse
  M4aHerbrand.GenuineDescent

theorem LanglandsTunnell.Converse.isAdmissibleTwist_comp_idelicNorm_genuineBaseChange
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (η : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hη : IsAdmissibleTwist E η) :
    IsAdmissibleTwist M (η.comp (genuineBaseChange E M).idelicNorm) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_isAdmissibleTwist_comp_idelicNorm_genuineBaseChange.solution
