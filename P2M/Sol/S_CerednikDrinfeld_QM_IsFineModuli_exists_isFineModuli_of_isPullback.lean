import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuli_of_isPullback

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {B B' : Type} [CommRing B] [CommRing B'] (β : B →+* B')
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {M' : Scheme.{0}} (πM' : M' ⟶ Spec (CommRingCat.of B')) (pr : M' ⟶ M)
    (hpr : CategoryTheory.IsPullback pr πM' πM (Spec.map (CommRingCat.ofHom β))) :
    ∃ ptF' : (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B')),
        FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM'),
      IsFineModuli Λ N m M' πM' ptF' ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B'))
        (u : FakeEllipticCurve.WithFullLevel Λ N m S),
        (ptF' S s u).1 ≫ pr = (ptF S (s ≫ Spec.map (CommRingCat.ofHom β)) u).1 := by
  let ptF' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B')),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM' :=
    fun S _ s u => ⟨hpr.lift (ptF S (s ≫ Spec.map (CommRingCat.ofHom β)) u).1 s
        (ptF S (s ≫ Spec.map (CommRingCat.ofHom β)) u).2, hpr.lift_snd _ _ _⟩
  have hval : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B'))
      (u : FakeEllipticCurve.WithFullLevel Λ N m S),
      (ptF' S s u).1 ≫ pr = (ptF S (s ≫ Spec.map (CommRingCat.ofHom β)) u).1 :=
    fun S _ s u => hpr.lift_fst _ _ _
  refine ⟨ptF', ⟨?_, ?_, ?_, ?_⟩, hval⟩
  ·
    intro S _ s u u' h
    apply Subtype.ext
    apply hpr.hom_ext
    · rw [hval, hval, hM.ptF_iso S _ u u' h]
    · rw [(ptF' S s u).2, (ptF' S s u').2]
  ·
    intro S S' _ _ φ s s' hss' u u' h
    apply hpr.hom_ext
    · rw [hval, Category.assoc, hval]
      exact hM.ptF_pullback S S' φ _ _ (by rw [← Category.assoc, hss']) u u' h
    · rw [(ptF' S' s' u').2, Category.assoc, (ptF' S s u).2, hss']
  ·
    intro S _ s x
    obtain ⟨u, hu⟩ := hM.ptF_surjective S (s ≫ Spec.map (CommRingCat.ofHom β))
      ⟨x.1 ≫ pr, by rw [Category.assoc, hpr.w, ← Category.assoc, x.2]⟩
    refine ⟨u, Subtype.ext (hpr.hom_ext ?_ ?_)⟩
    · rw [hval, hu]
    · rw [(ptF' S s u).2, x.2]
  ·
    intro S _ s u u' h
    apply hM.ptF_injective S (s ≫ Spec.map (CommRingCat.ofHom β))
    apply Subtype.ext
    rw [← hval, ← hval, h]
