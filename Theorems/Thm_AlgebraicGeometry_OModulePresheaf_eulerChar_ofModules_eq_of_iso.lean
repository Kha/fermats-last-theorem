import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_eq_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.OModulePresheaf.eulerChar_ofModules_eq_of_iso
    {R : Type} [CommRing R] {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of R))
    (M M' : V.Modules) (e : M ≅ M') (𝒦 : V.OrderedAffineCover) :
    (OModulePresheaf.ofModules π M).eulerChar 𝒦 = (OModulePresheaf.ofModules π M').eulerChar 𝒦 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_eq_of_iso.solution
