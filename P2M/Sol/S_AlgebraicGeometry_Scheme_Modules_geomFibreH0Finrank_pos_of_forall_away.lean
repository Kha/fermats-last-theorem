import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_away

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u v

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (A' : Fin k → Scheme.{u}) (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
    (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))))
    (𝓛 : A.Modules)
    (hloc : ∀ (i : Fin k) (K : Type u) [Field K] [IsAlgClosed K] (sk' : Localization.Away (r i) →+* K),
      0 < Scheme.Modules.geomFibreH0Finrank (f' i) ((Scheme.Modules.pullback (g i)).obj 𝓛) K sk') :
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (sk : S →+* K), 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 K sk := by
  classical
  intro K _ _ sk

  have hi : ∃ i, sk (r i) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hle : Ideal.span (Set.range r) ≤ RingHom.ker sk := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hcon i)
    rw [hr, top_le_iff] at hle
    exact (RingHom.ker_ne_top sk) hle
  obtain ⟨i, hi⟩ := hi
  let sk' : Localization.Away (r i) →+* K := IsLocalization.Away.lift (r i) (isUnit_iff_ne_zero.mpr hi)
  have hsk : sk'.comp (algebraMap S (Localization.Away (r i))) = sk := IsLocalization.Away.lift_comp (r i) _
  have h := hloc i K sk'
  rw [AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback (algebraMap S (Localization.Away (r i))) f (f' i) (g i) (hg i) 𝓛 _ (Iso.refl _) K sk', hsk] at h
  exact h
