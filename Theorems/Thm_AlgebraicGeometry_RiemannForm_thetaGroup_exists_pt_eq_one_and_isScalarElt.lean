import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_pt_eq_one_and_isScalarElt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.thetaGroup.exists_pt_eq_one_and_isScalarElt
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M : A.Modules) (c : k) (hc0 : c ≠ 0) :
    ∃ g : thetaGroup f L hc M, thetaGroup.pt f L hc M g = 1 ∧ thetaGroup.IsScalarElt f L hc M g c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_pt_eq_one_and_isScalarElt.solution
