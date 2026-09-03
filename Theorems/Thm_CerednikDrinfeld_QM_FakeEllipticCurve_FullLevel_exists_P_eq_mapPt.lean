import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_mapPt

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_mapPt
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N N' : ℕ} {S : Type u} [CommRing S] {m : ℕ}
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N' S)
    (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x)
    (P : E.FullLevel m) :
    ∃ P' : E'.FullLevel m, P'.P = mapPt e.hom he P.P := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_mapPt.solution
