import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_MvFormalGroup_Deformation
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_exists_deformation_isFormalCoordinates_liftsCoordinates
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct
theorem GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (Ĝ₁ : MvFormalGroup 2 B₁) (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2) (hθ₁ : L₁.IsFormalCoordinates Ĝ₁ θ₁)
    (D : BareDeformation f₁ L₁ B) :
    ∃ (G : MvFormalGroup.Deformation Ĝ₁ B) (θ : RelativeGroupLaw.FormalCoordinates D.f 2),
      G.F.IsComm ∧ D.L.IsFormalCoordinates G.F θ ∧ D.LiftsCoordinates θ₁ θ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_exists_deformation_isFormalCoordinates_liftsCoordinates.solution
