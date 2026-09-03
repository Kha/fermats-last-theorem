import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop
    {S S' : Scheme.{u}} (p : S' ⟶ S)
    (e : SheafOfModules.unit S.ringCatSheaf ≅ SheafOfModules.unit S.ringCatSheaf) :
    ((((Scheme.Modules.pullbackUnitIso p).symm ≪≫ (Scheme.Modules.pullback p).mapIso e ≪≫
          Scheme.Modules.pullbackUnitIso p :
            SheafOfModules.unit S'.ringCatSheaf ≅ SheafOfModules.unit S'.ringCatSheaf)).hom.val.app (op ⊤)).hom
        (1 : S'.presheaf.obj (op ⊤)) =
      p.appTop.hom ((e.hom.val.app (op ⊤)).hom (1 : S.presheaf.obj (op ⊤))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop.solution
