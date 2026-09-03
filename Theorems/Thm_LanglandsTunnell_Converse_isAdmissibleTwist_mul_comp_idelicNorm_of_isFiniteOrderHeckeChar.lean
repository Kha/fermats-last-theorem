import Mathlib
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar

set_option autoImplicit false

open NumberField HeckeCharacter LanglandsTunnell.Converse M4aHerbrand.GenuineDescent

theorem LanglandsTunnell.Converse.isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist E μ) :
    IsAdmissibleTwist M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar.solution
