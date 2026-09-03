import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_isPullback

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isAtkinLehnerQuotient_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (r : ℕ)
    (v v₁ : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (v' v₁' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (hv : (∃ (g : v'.1.A ⟶ v.1.A)
        (hg : CategoryTheory.IsPullback g v'.1.f v.1.f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q Q' : SchemeHomOver t' v'.1.f),
        (v'.1.L.mul t' Q Q').1 ≫ g =
          (v.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩
            ⟨Q'.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q'.2]⟩).1) ∧
      (∀ x : ↥Λ, v'.1.act x ≫ g = g ≫ v.1.act x) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q : SchemeHomOver t' v'.1.f),
        (QM.FactorsThrough v'.1.lev Q → ∃ Q₀ : T ⟶ v.1.C, Q₀ ≫ v.1.lev = Q.1 ≫ g) ∧
        (QM.FactorsThrough v'.2.levK Q → ∃ Q₀ : T ⟶ v.2.K, Q₀ ≫ v.2.levK = Q.1 ≫ g))))
    (hv₁ : (∃ (g : v₁'.1.A ⟶ v₁.1.A)
        (hg : CategoryTheory.IsPullback g v₁'.1.f v₁.1.f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q Q' : SchemeHomOver t' v₁'.1.f),
        (v₁'.1.L.mul t' Q Q').1 ≫ g =
          (v₁.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩
            ⟨Q'.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q'.2]⟩).1) ∧
      (∀ x : ↥Λ, v₁'.1.act x ≫ g = g ≫ v₁.1.act x) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q : SchemeHomOver t' v₁'.1.f),
        (QM.FactorsThrough v₁'.1.lev Q → ∃ Q₀ : T ⟶ v₁.1.C, Q₀ ≫ v₁.1.lev = Q.1 ≫ g) ∧
        (QM.FactorsThrough v₁'.2.levK Q → ∃ Q₀ : T ⟶ v₁.2.K, Q₀ ≫ v₁.2.levK = Q.1 ≫ g))))
    (h : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r v v₁) :
    QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r v' v₁' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_isPullback.solution
