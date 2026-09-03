import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_iff_apply_closedPoint_mem_range

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {K : Type u} [Field K] (x : Spec (CommRingCat.of K) ⟶ X) :
    (∃ z : Spec (CommRingCat.of K) ⟶ Z, z ≫ i = x) ↔
      x.base (IsLocalRing.closedPoint K) ∈ Set.range i.base := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · intro hmem

    have hpt : ∀ p : ↥(Spec (CommRingCat.of K)), p = IsLocalRing.closedPoint K := fun p =>
      ((PrimeSpectrum.instUnique (R := (CommRingCat.of K))).uniq p).trans
        ((PrimeSpectrum.instUnique (R := (CommRingCat.of K))).uniq (IsLocalRing.closedPoint K)).symm
    have hsurj : Surjective (pullback.fst x i) := by
      refine ⟨fun p => ?_⟩
      obtain ⟨y, hy⟩ := hmem
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := i)
        (IsLocalRing.closedPoint K) y hy.symm
      exact ⟨w, by rw [hpt p]; exact hw⟩
    have : IsIso (pullback.fst x i) := isIso_of_isClosedImmersion_of_surjective _
    refine ⟨inv (pullback.fst x i) ≫ pullback.snd x i, ?_⟩
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
