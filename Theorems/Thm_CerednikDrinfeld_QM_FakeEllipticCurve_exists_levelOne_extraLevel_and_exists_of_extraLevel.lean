import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelOne_extraLevel_and_exists_of_extraLevel

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_levelOne_extraLevel_and_exists_of_extraLevel
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) (S : Type u) [CommRing S] :
    (∀ E : FakeEllipticCurve Λ N S,
      ∃ (E₁ : FakeEllipticCurve Λ 1 S) (K : E₁.ExtraLevel N) (e : E.A ≅ E₁.A) (he : e.hom ≫ E₁.f = E.f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
          mapPt e.hom he (E.L.mul t P Q) = E₁.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E₁.act x) ∧
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P ↔ FactorsThrough K.levK (mapPt e.hom he P))) ∧
    (∀ (E₁ : FakeEllipticCurve Λ 1 S) (K : E₁.ExtraLevel N),
      ∃ (E : FakeEllipticCurve Λ N S) (e : E.A ≅ E₁.A) (he : e.hom ≫ E₁.f = E.f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
          mapPt e.hom he (E.L.mul t P Q) = E₁.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E₁.act x) ∧
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P ↔ FactorsThrough K.levK (mapPt e.hom he P))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelOne_extraLevel_and_exists_of_extraLevel.solution
