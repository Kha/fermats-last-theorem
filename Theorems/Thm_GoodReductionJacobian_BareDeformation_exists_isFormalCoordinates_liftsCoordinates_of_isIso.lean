import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_MvFormalGroup_Deformation
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_liftsCoordinates_of_isIso
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct
theorem GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_isIso
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (Ĝ₁ : MvFormalGroup 2 B₁) (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2)
    (D : BareDeformation f₁ L₁ B) (G G' : MvFormalGroup.Deformation Ĝ₁ B)
    (θ : RelativeGroupLaw.FormalCoordinates D.f 2)
    (hθ : D.L.IsFormalCoordinates G.F θ) (hl : D.LiftsCoordinates θ₁ θ) (hiso : G.IsIso G') :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates D.f 2, D.L.IsFormalCoordinates G'.F θ' ∧ D.LiftsCoordinates θ₁ θ' := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_liftsCoordinates_of_isIso.solution
