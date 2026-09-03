import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsLevelTwistAction_finite_of_isOrder

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.IsLevelTwistAction.finite_of_isOrder
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {N m : ℕ} (hm : 0 < m)
    {B : Type} [CommRing B] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ}
    (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ) : Finite G := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsLevelTwistAction_finite_of_isOrder.solution
