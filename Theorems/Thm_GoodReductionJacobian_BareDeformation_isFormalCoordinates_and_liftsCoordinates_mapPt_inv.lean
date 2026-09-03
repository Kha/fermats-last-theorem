import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_isFormalCoordinates_and_liftsCoordinates_mapPt_inv

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped TensorProduct
theorem GoodReductionJacobian.BareDeformation.isFormalCoordinates_and_liftsCoordinates_mapPt_inv
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁} {d : ℕ}
    (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ d)
    (D D' : BareDeformation f₁ L₁ B) (e : D.A ≅ D'.A) (he : e.hom ≫ D'.f = D.f) (hg : D.g ≫ e.hom = D'.g)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
      mapPt e.hom he (D.L.mul t P Q) = D'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (F' : MvFormalGroup d B) (θ' : RelativeGroupLaw.FormalCoordinates D'.f d)
    (hθ' : D'.L.IsFormalCoordinates F' θ') (hl' : D'.LiftsCoordinates θ₁ θ') :
    D.L.IsFormalCoordinates F'
        (fun B'' _ _ s => mapPt e.inv (by rw [← he, e.inv_hom_id_assoc]) (θ' B'' s)) ∧
      D.LiftsCoordinates θ₁ (fun B'' _ _ s => mapPt e.inv (by rw [← he, e.inv_hom_id_assoc]) (θ' B'' s)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_isFormalCoordinates_and_liftsCoordinates_mapPt_inv.solution
