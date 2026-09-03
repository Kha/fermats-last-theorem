import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isoTVia_unique_comp_transport_trans

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.isoTVia_unique_comp_transport_trans
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m ℓ : ℕ) :

    (∀ (S B : Type) [CommRing S] [CommRing B] (χ : S →+* B)
        (u : FakeEllipticCurve.WithFullLevel Λ N m S) (Cu : u.1.ExtraLevel ℓ)
        (v v' : FakeEllipticCurve.WithFullLevel Λ N m B) (Cv : v.1.ExtraLevel ℓ) (Cv' : v'.1.ExtraLevel ℓ)
        (g : v.1.A ⟶ u.1.A) (g' : v'.1.A ⟶ u.1.A),
        FakeEllipticCurve.IsPullbackVia χ u.1 v.1 g → (v.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom χ) ≫ (u.2.P).1 →
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t' v.1.f),
          FactorsThrough Cv.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g) →
        FakeEllipticCurve.IsPullbackVia χ u.1 v'.1 g' → (v'.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom χ) ≫ (u.2.P).1 →
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t' v'.1.f),
          FactorsThrough Cv'.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g') →
        ∃ (e : v.1.A ≅ v'.1.A) (he : e.hom ≫ v'.1.f = v.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia v v' Cv Cv' e he) ∧

    (∀ (S S' S'' : Type) [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
        (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S')
        (u'' : FakeEllipticCurve.WithFullLevel Λ N m S'')
        (Cu : u.1.ExtraLevel ℓ) (Cu' : u'.1.ExtraLevel ℓ) (Cu'' : u''.1.ExtraLevel ℓ)
        (g : u'.1.A ⟶ u.1.A) (g' : u''.1.A ⟶ u'.1.A),
        FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g → (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1 →
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
          FactorsThrough Cu'.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g) →
        FakeEllipticCurve.IsPullbackVia ψ u'.1 u''.1 g' → (u''.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom ψ) ≫ (u'.2.P).1 →
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S'')) (P : SchemeHomOver t' u''.1.f),
          FactorsThrough Cu''.levK P → ∃ P₀ : T₀ ⟶ Cu'.K, P₀ ≫ Cu'.levK = P.1 ≫ g') →
        FakeEllipticCurve.IsPullbackVia (ψ.comp φ) u.1 u''.1 (g' ≫ g) ∧ (u''.2.P).1 ≫ (g' ≫ g) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ (u.2.P).1 ∧
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S'')) (P : SchemeHomOver t' u''.1.f),
          FactorsThrough Cu''.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ (g' ≫ g))) ∧

    (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (u w : FakeEllipticCurve.WithFullLevel Λ N m S) (Cu : u.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ)
        (e : u.1.A ≅ w.1.A) (he : e.hom ≫ w.1.f = u.1.f),
        FakeEllipticCurve.WithFullLevel.IsoTVia u w Cu Cw e he →
        ∀ (u' : FakeEllipticCurve.WithFullLevel Λ N m S') (Cu' : u'.1.ExtraLevel ℓ) (g : u'.1.A ⟶ u.1.A),
        FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g → (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1 →
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
          FactorsThrough Cu'.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g) →
        FakeEllipticCurve.IsPullbackVia φ w.1 u'.1 (g ≫ e.hom) ∧ (u'.2.P).1 ≫ (g ≫ e.hom) = Spec.map (CommRingCat.ofHom φ) ≫ (w.2.P).1 ∧
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
          FactorsThrough Cu'.levK P → ∃ P₀ : T₀ ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ (g ≫ e.hom))) ∧

    (∀ (S : Type) [CommRing S] (u v w : FakeEllipticCurve.WithFullLevel Λ N m S)
        (Cu : u.1.ExtraLevel ℓ) (Cv : v.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ),
        (∃ (e : u.1.A ≅ v.1.A) (he : e.hom ≫ v.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia u v Cu Cv e he) → (∃ (e : v.1.A ≅ w.1.A) (he : e.hom ≫ w.1.f = v.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia v w Cv Cw e he) →
        ∃ (e : u.1.A ≅ w.1.A) (he : e.hom ≫ w.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia u w Cu Cw e he) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isoTVia_unique_comp_transport_trans.solution
