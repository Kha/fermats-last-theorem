import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsCoarseModuli_exists_hom_pullback_bijective_points

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsCoarseModuli.exists_hom_pullback_bijective_points
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ)
    {B₀ B₁ : Type} [CommRing B₀] [CommRing B₁] (ι : Spec (CommRingCat.of B₁) ⟶ Spec (CommRingCat.of B₀))

    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of B₀))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
      FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B₀)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₀))
      (x : SchemeHomOver s f), ∃ E : FakeEllipticCurve Λ N k, pt k s E = x)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₀))
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')

    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B₁))
    (ptX : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hX : IsCoarseModuli Λ N X πX ptX) :
    ∃ h : X ⟶ pullback f ι,
      h ≫ pullback.snd f ι = πX ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁))
        (E : FakeEllipticCurve Λ N S), (ptX S s E).1 ≫ h ≫ pullback.fst f ι = (pt S (s ≫ ι) E).1) ∧
      (∀ h' : X ⟶ pullback f ι, h' ≫ pullback.snd f ι = πX →
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁))
          (E : FakeEllipticCurve Λ N S), (ptX S s E).1 ≫ h' ≫ pullback.fst f ι = (pt S (s ≫ ι) E).1) →
        h' = h) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₁))
        (P P' : SchemeHomOver s πX), P.1 ≫ h = P'.1 ≫ h → P = P') ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₁))
        (Q : SchemeHomOver s (pullback.snd f ι)), ∃ P : SchemeHomOver s πX, P.1 ≫ h = Q.1) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsCoarseModuli_exists_hom_pullback_bijective_points.solution
