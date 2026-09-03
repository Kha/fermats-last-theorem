import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mapPt_mapPt_mul_zpow_eq_zpow_sub_of_mapPt_mapPt_mul_zpow_eq_zpow

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u
theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_mapPt_mapPt_mul_zpow_eq_zpow_sub_of_mapPt_mapPt_mul_zpow_eq_zpow
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (t n k : ℤ)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hadd : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver s E.f),
      mapPt φ hφ (E.L.mul s P Q) = E.L.mul s (mapPt φ hφ P) (mapPt φ hφ Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (hrel : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t) :
    ∃ (ψ : E.A ⟶ E.A) (hψ : ψ ≫ E.f = E.f),
      (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver s E.f),
          mapPt ψ hψ (E.L.mul s P Q) = E.L.mul s (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ ψ = ψ ≫ E.act x) ∧
      (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver s E.f),
          letI := E.L.pointCommGroup E.comm s
          mapPt ψ hψ P = mapPt φ hφ P * P ^ (-k)) ∧
      ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver s E.f),
        letI := E.L.pointCommGroup E.comm s
        mapPt ψ hψ (mapPt ψ hψ P) * P ^ (k ^ 2 - t * k + n) = mapPt ψ hψ P ^ (t - 2 * k) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mapPt_mapPt_mul_zpow_eq_zpow_sub_of_mapPt_mapPt_mul_zpow_eq_zpow.solution
