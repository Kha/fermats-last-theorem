import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_app_tensorObj
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullbackComp_app_tensorObj
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    (Scheme.Modules.pullbackComp f g).app (M ⊗ N) =
      (Scheme.Modules.pullback f).mapIso (Scheme.Modules.pullbackTensorObjIso g M N) ≪≫
        Scheme.Modules.pullbackTensorObjIso f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N) ≪≫
        ((Scheme.Modules.pullbackComp f g).app M ⊗ᵢ (Scheme.Modules.pullbackComp f g).app N) ≪≫
        (Scheme.Modules.pullbackTensorObjIso (f ≫ g) M N).symm := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_app_tensorObj.solution
