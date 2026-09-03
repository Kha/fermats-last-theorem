import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_hom_pullback_bijective_points

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsCoarseModuliT.exists_hom_pullback_bijective_points
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ)
    {B₀ B₁ : Type} [CommRing B₀] [CommRing B₁] (ι : Spec (CommRingCat.of B₁) ⟶ Spec (CommRingCat.of B₀))

    (𝒴 : Scheme.{0}) (g : 𝒴 ⟶ Spec (CommRingCat.of B₀))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s g)
    (ptT_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀))
      (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), FakeEllipticCurve.WithExtraLevel.Iso u u' → ptT S s u = ptT S s u')
    (ptT_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B₀)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
      FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (ptT S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptT S s u).1)
    (ptT_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₀))
      (y : SchemeHomOver s g), ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k, ptT k s u = y)
    (ptT_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₀))
      (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ k), ptT k s u = ptT k s u' → FakeEllipticCurve.WithExtraLevel.Iso u u')

    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of B₁))
    (ptY : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY)
    (hY : IsCoarseModuliT Λ N ℓ Y πY ptY) :
    ∃ h : Y ⟶ pullback g ι,
      h ≫ pullback.snd g ι = πY ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁))
        (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), (ptY S s u).1 ≫ h ≫ pullback.fst g ι = (ptT S (s ≫ ι) u).1) ∧
      (∀ h' : Y ⟶ pullback g ι, h' ≫ pullback.snd g ι = πY →
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁))
          (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), (ptY S s u).1 ≫ h' ≫ pullback.fst g ι = (ptT S (s ≫ ι) u).1) →
        h' = h) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₁))
        (P P' : SchemeHomOver s πY), P.1 ≫ h = P'.1 ≫ h → P = P') ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₁))
        (Q : SchemeHomOver s (pullback.snd g ι)), ∃ P : SchemeHomOver s πY, P.1 ≫ h = Q.1) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_hom_pullback_bijective_points.solution
