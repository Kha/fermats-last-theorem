import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_comp_eq_and_isIso

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {B : Type} [CommRing B]
    {Y : Scheme.{0}} {πY : Y ⟶ Spec (CommRingCat.of B)}
    {ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY}
    (hY : IsCoarseModuliT Λ N ℓ Y πY ptT)
    {Y' : Scheme.{0}} {πY' : Y' ⟶ Spec (CommRingCat.of B)}
    {ptT' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY'}
    (hY' : IsCoarseModuliT Λ N ℓ Y' πY' ptT') :
    (∃! g : Y ⟶ Y', g ≫ πY' = πY ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (ptT' S s u).1 = (ptT S s u).1 ≫ g) ∧
    ∀ g : Y ⟶ Y', g ≫ πY' = πY →
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (ptT' S s u).1 = (ptT S s u).1 ≫ g) → IsIso g := by
  obtain ⟨g, ⟨hg1, hg2⟩, hguniq⟩ := hY.univ Y' πY' ptT' hY'.ptT_iso hY'.ptT_pullback
  obtain ⟨g', ⟨hg'1, hg'2⟩, -⟩ := hY'.univ Y πY ptT hY.ptT_iso hY.ptT_pullback
  have h1 : g ≫ g' = 𝟙 _ := by
    apply (hY.univ Y πY ptT hY.ptT_iso hY.ptT_pullback).unique
    · exact ⟨by rw [Category.assoc, hg'1, hg1], fun S _ s E => by rw [← Category.assoc, ← hg2 S s E, ← hg'2 S s E]⟩
    · exact ⟨by simp, fun S _ s E => by simp⟩
  have h2 : g' ≫ g = 𝟙 _ := by
    apply (hY'.univ Y' πY' ptT' hY'.ptT_iso hY'.ptT_pullback).unique
    · exact ⟨by rw [Category.assoc, hg1, hg'1], fun S _ s E => by rw [← Category.assoc, ← hg'2 S s E, ← hg2 S s E]⟩
    · exact ⟨by simp, fun S _ s E => by simp⟩
  refine ⟨⟨g, ⟨hg1, hg2⟩, fun y hy => hguniq y hy⟩, fun k hk1 hk2 => ?_⟩
  have hk : k = g := hguniq k ⟨hk1, hk2⟩
  subst hk
  exact ⟨⟨g', h1, h2⟩⟩
