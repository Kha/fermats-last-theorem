import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isPullback_refl_comp_cancel_iso_unique_nsmulPt

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.isPullback_refl_comp_cancel_iso_unique_nsmulPt
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N k : ℕ) :
    (∀ (S : Type u) [CommRing S] (u : FakeEllipticCurve.WithFullLevel Λ N k S),
        FakeEllipticCurve.WithFullLevel.IsPullback (RingHom.id S) u u) ∧
    (∀ (S S' S'' : Type u) [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
        (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' : FakeEllipticCurve.WithFullLevel Λ N k S')
        (u'' : FakeEllipticCurve.WithFullLevel Λ N k S''),
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → FakeEllipticCurve.WithFullLevel.IsPullback ψ u' u'' →
          FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'') ∧
    (∀ (S S' S'' : Type u) [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
        (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' : FakeEllipticCurve.WithFullLevel Λ N k S')
        (u'' : FakeEllipticCurve.WithFullLevel Λ N k S''),
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'' →
          FakeEllipticCurve.WithFullLevel.IsPullback ψ u' u'') ∧
    (∀ (S S' : Type u) [CommRing S] [CommRing S'] (φ : S →+* S')
        (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' u'' : FakeEllipticCurve.WithFullLevel Λ N k S'),
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → FakeEllipticCurve.WithFullLevel.Iso u' u'' →
          FakeEllipticCurve.WithFullLevel.IsPullback φ u u'') ∧
    (∀ (S S' : Type u) [CommRing S] [CommRing S'] (φ : S →+* S')
        (u₁ u₂ : FakeEllipticCurve.WithFullLevel Λ N k S) (u' : FakeEllipticCurve.WithFullLevel Λ N k S'),
        FakeEllipticCurve.WithFullLevel.Iso u₁ u₂ → FakeEllipticCurve.WithFullLevel.IsPullback φ u₁ u' →
          FakeEllipticCurve.WithFullLevel.IsPullback φ u₂ u') ∧
    (∀ (S S' : Type u) [CommRing S] [CommRing S'] (φ : S →+* S')
        (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' u'' : FakeEllipticCurve.WithFullLevel Λ N k S'),
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → FakeEllipticCurve.WithFullLevel.IsPullback φ u u'' →
          FakeEllipticCurve.WithFullLevel.Iso u' u'') ∧
    (∀ (n k' : ℕ) (S S' : Type u) [CommRing S] [CommRing S'] (φ : S →+* S')
        (u : FakeEllipticCurve.WithFullLevel Λ N k S) (u' : FakeEllipticCurve.WithFullLevel Λ N k S')
        (P : u.1.FullLevel k'), P.P = nsmulPt u.1.L (𝟙 (Spec (CommRingCat.of S))) n u.2.P →
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' →
          ∃ P' : u'.1.FullLevel k', P'.P = nsmulPt u'.1.L (𝟙 (Spec (CommRingCat.of S'))) n u'.2.P ∧
            FakeEllipticCurve.WithFullLevel.IsPullback φ (⟨u.1, P⟩ : FakeEllipticCurve.WithFullLevel Λ N k' S)
              ⟨u'.1, P'⟩) ∧
    (∀ (n k' : ℕ) (S : Type u) [CommRing S] (u₁ u₂ : FakeEllipticCurve.WithFullLevel Λ N k S)
        (Q₁ : u₁.1.FullLevel k') (Q₂ : u₂.1.FullLevel k'),
        Q₁.P = nsmulPt u₁.1.L (𝟙 (Spec (CommRingCat.of S))) n u₁.2.P →
        Q₂.P = nsmulPt u₂.1.L (𝟙 (Spec (CommRingCat.of S))) n u₂.2.P →
        FakeEllipticCurve.WithFullLevel.Iso u₁ u₂ →
          FakeEllipticCurve.WithFullLevel.Iso (⟨u₁.1, Q₁⟩ : FakeEllipticCurve.WithFullLevel Λ N k' S) ⟨u₂.1, Q₂⟩) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isPullback_refl_comp_cancel_iso_unique_nsmulPt.solution
