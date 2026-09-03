import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_map_liftsCoordinates

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
theorem GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_map_liftsCoordinates
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D : BareDeformation f₁ L₁ B) {g : ℕ} (F : MvFormalGroup g B)
    (θ : RelativeGroupLaw.FormalCoordinates D.f g) (hθ : D.L.IsFormalCoordinates F θ) :
    ∃ θ₁ : RelativeGroupLaw.FormalCoordinates f₁ g,
      L₁.IsFormalCoordinates (F.map (algebraMap B B₁)) θ₁ ∧ D.LiftsCoordinates θ₁ θ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_map_liftsCoordinates.solution
