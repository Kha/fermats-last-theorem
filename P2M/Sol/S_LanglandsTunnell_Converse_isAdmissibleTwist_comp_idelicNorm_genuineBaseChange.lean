import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import P2M.Util
namespace P2MW.S_LanglandsTunnell_Converse_isAdmissibleTwist_comp_idelicNorm_genuineBaseChange

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain LanglandsTunnell.Converse M4aHerbrand.GenuineDescent

namespace LTIdelicNormBaseChange

variable (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]

theorem idelicNorm_principal (u : Mˣ) :
    (genuineBaseChange E M).idelicNorm (Units.map (algebraMap M (AdeleRing (𝓞 M) M) : M →* _) u) =
      Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* _) (Units.map (Algebra.norm E : M →* E) u) := by
  refine Units.ext ?_
  show (genuineBaseChange E M).adelicNorm (algebraMap M (AdeleRing (𝓞 M) M) (u : M)) =
    algebraMap E (AdeleRing (𝓞 E) E) (Algebra.norm E (u : M))
  exact adelicNorm_genuineBaseChange_algebraMap E M (u : M)

theorem continuous_idelicNorm : Continuous (genuineBaseChange E M).idelicNorm :=
  Continuous.units_map _ (continuous_adelicNorm_genuineBaseChange E M)

end LTIdelicNormBaseChange

theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (η : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hη : IsAdmissibleTwist E η) :
    IsAdmissibleTwist M (η.comp (genuineBaseChange E M).idelicNorm) := by
  obtain ⟨hcl, hcont, hun⟩ := hη
  refine ⟨?_, ?_, ?_⟩
  · intro u
    rw [MonoidHom.comp_apply, LTIdelicNormBaseChange.idelicNorm_principal E M u]
    exact hcl _
  · exact hcont.comp (LTIdelicNormBaseChange.continuous_idelicNorm E M)
  · intro x
    exact hun _
