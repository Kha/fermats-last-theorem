import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_thetaGroup_eq_one_of_isScalarElt_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.thetaGroup.eq_one_of_isScalarElt_one
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M : A.Modules)
    (g : thetaGroup f L hc M) (h : thetaGroup.IsScalarElt f L hc M g 1) :
    g = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_eq_one_of_isScalarElt_one.solution
