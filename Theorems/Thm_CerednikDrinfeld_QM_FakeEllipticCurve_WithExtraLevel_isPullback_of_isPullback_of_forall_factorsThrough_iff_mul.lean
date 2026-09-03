import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isPullback_of_isPullback_of_forall_factorsThrough_iff_mul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isPullback_of_isPullback_of_forall_factorsThrough_iff_mul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ (N * ℓ) S) (E' : FakeEllipticCurve Λ (N * ℓ) S') (h : FakeEllipticCurve.IsPullback φ E E')
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    (e : u.1.A ≅ E.A) (he : e.hom ≫ E.f = u.1.f)
    (e_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = E.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (e_act : ∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ E.act x)
    (e_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔
        FactorsThrough E.lev (mapPt e.hom he P) ∧ nsmulPt E.L t N (mapPt e.hom he P) = E.L.one t)
    (e_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.2.levK P ↔
        FactorsThrough E.lev (mapPt e.hom he P) ∧ nsmulPt E.L t ℓ (mapPt e.hom he P) = E.L.one t)
    (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (e' : u'.1.A ≅ E'.A) (he' : e'.hom ≫ E'.f = u'.1.f)
    (e'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t u'.1.f),
      mapPt e'.hom he' (u'.1.L.mul t P Q) = E'.L.mul t (mapPt e'.hom he' P) (mapPt e'.hom he' Q))
    (e'_act : ∀ x : ↥Λ, u'.1.act x ≫ e'.hom = e'.hom ≫ E'.act x)
    (e'_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t u'.1.f),
      FactorsThrough u'.1.lev P ↔
        FactorsThrough E'.lev (mapPt e'.hom he' P) ∧ nsmulPt E'.L t N (mapPt e'.hom he' P) = E'.L.one t)
    (e'_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t u'.1.f),
      FactorsThrough u'.2.levK P ↔
        FactorsThrough E'.lev (mapPt e'.hom he' P) ∧ nsmulPt E'.L t ℓ (mapPt e'.hom he' P) = E'.L.one t) :
    FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isPullback_of_isPullback_of_forall_factorsThrough_iff_mul.solution
