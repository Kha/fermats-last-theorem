import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_transportIso_tensorObj
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.transportIso_tensorObj
    {A : Scheme.{0}} {T g : A ⟶ A} (h : T ≫ g = g) (M M' : A.Modules) :
    transportIso h (M ⊗ M') =
      (Scheme.Modules.pullback T).mapIso (Scheme.Modules.pullbackTensorObjIso g M M') ≪≫
        Scheme.Modules.pullbackTensorObjIso T ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj M') ≪≫
        (transportIso h M ⊗ᵢ transportIso h M') ≪≫
        (Scheme.Modules.pullbackTensorObjIso g M M').symm := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_transportIso_tensorObj.solution
