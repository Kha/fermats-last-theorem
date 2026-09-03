import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_HeckeCharacter_isAdjuster_unitsMap_genuineBaseChange_one_of_isAdjuster_one

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative

theorem HeckeCharacter.isAdjuster_unitsMap_genuineBaseChange_one_of_isAdjuster_one
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (𝔣 : Ideal (𝓞 E)) (u : (AdeleRing (𝓞 E) E)ˣ) (hu : IsAdjuster E 𝔣 u 1) :
    IsAdjuster F (modulusExt E F 𝔣) (Units.map (genuineBaseChange E F).β.toMonoidHom u) 1 := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_isAdjuster_unitsMap_genuineBaseChange_one_of_isAdjuster_one.solution
