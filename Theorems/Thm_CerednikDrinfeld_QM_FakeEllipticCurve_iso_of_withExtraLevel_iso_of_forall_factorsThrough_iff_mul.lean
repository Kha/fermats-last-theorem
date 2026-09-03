import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} (hNℓ : N.Coprime ℓ) {S : Type} [CommRing S]
    (u₁ u₂ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (h : FakeEllipticCurve.WithExtraLevel.Iso u₁ u₂)
    (E₁ : FakeEllipticCurve Λ (N * ℓ) S)
    (e₁ : u₁.1.A ≅ E₁.A) (he₁ : e₁.hom ≫ E₁.f = u₁.1.f)
    (e₁_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u₁.1.f),
      mapPt e₁.hom he₁ (u₁.1.L.mul t P Q) = E₁.L.mul t (mapPt e₁.hom he₁ P) (mapPt e₁.hom he₁ Q))
    (e₁_act : ∀ x : ↥Λ, u₁.1.act x ≫ e₁.hom = e₁.hom ≫ E₁.act x)
    (e₁_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₁.1.f),
      FactorsThrough u₁.1.lev P ↔
        FactorsThrough E₁.lev (mapPt e₁.hom he₁ P) ∧ nsmulPt E₁.L t N (mapPt e₁.hom he₁ P) = E₁.L.one t)
    (e₁_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₁.1.f),
      FactorsThrough u₁.2.levK P ↔
        FactorsThrough E₁.lev (mapPt e₁.hom he₁ P) ∧ nsmulPt E₁.L t ℓ (mapPt e₁.hom he₁ P) = E₁.L.one t)
    (E₂ : FakeEllipticCurve Λ (N * ℓ) S)
    (e₂ : u₂.1.A ≅ E₂.A) (he₂ : e₂.hom ≫ E₂.f = u₂.1.f)
    (e₂_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u₂.1.f),
      mapPt e₂.hom he₂ (u₂.1.L.mul t P Q) = E₂.L.mul t (mapPt e₂.hom he₂ P) (mapPt e₂.hom he₂ Q))
    (e₂_act : ∀ x : ↥Λ, u₂.1.act x ≫ e₂.hom = e₂.hom ≫ E₂.act x)
    (e₂_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₂.1.f),
      FactorsThrough u₂.1.lev P ↔
        FactorsThrough E₂.lev (mapPt e₂.hom he₂ P) ∧ nsmulPt E₂.L t N (mapPt e₂.hom he₂ P) = E₂.L.one t)
    (e₂_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₂.1.f),
      FactorsThrough u₂.2.levK P ↔
        FactorsThrough E₂.lev (mapPt e₂.hom he₂ P) ∧ nsmulPt E₂.L t ℓ (mapPt e₂.hom he₂ P) = E₂.L.one t) :
    FakeEllipticCurve.Iso E₁ E₂ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul.solution
