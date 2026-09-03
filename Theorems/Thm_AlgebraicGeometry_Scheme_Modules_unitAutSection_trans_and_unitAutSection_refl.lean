import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl
    {Y : Scheme.{u}} (W : Y.Opens) :
    (∀ e e' : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf,
        Scheme.Modules.unitAutSection W (e ≪≫ e') =
          Scheme.Modules.unitAutSection W e * Scheme.Modules.unitAutSection W e') ∧
      Scheme.Modules.unitAutSection W (Iso.refl _) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl.solution
