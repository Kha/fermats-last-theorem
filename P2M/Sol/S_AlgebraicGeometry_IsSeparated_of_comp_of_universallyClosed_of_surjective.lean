import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_IsSeparated_of_comp_of_universallyClosed_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsSeparated (f ≫ g)] [UniversallyClosed f]
    [Surjective f] : IsSeparated g := by

  let R : pullback f f ⟶ pullback (f ≫ g) (f ≫ g) :=
    pullback.map f f (f ≫ g) (f ≫ g) (𝟙 X) (𝟙 X) g (Category.id_comp _).symm
      (Category.id_comp _).symm
  let ff : pullback (f ≫ g) (f ≫ g) ⟶ pullback g g :=
    pullback.map (f ≫ g) (f ≫ g) g g f f (𝟙 _) (Category.comp_id _) (Category.comp_id _)
  have sq : IsPullback (pullback.fst f f ≫ f) R (pullback.diagonal g) ff :=
    pullback_map_diagonal_isPullback f f g

  have hR₁ : R ≫ pullback.fst (f ≫ g) (f ≫ g) = pullback.fst f f := by
    simp only [R, pullback.map, pullback.lift_fst, Category.comp_id]
  have : UniversallyClosed (R ≫ pullback.fst (f ≫ g) (f ≫ g)) := by rw [hR₁]; infer_instance
  have : IsSeparated (pullback.fst (f ≫ g) (f ≫ g)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : UniversallyClosed R := MorphismProperty.of_postcomp (W := @UniversallyClosed)
    (W' := @IsSeparated) R (pullback.fst (f ≫ g) (f ≫ g)) ‹_› ‹_›
  have hRcl : IsClosed (Set.range R) := by
    rw [← Set.image_univ]; exact R.isClosedMap _ isClosed_univ

  have hff₁ : Surjective ff :=
    MorphismProperty.pullbackMap (P := @Surjective) ‹Surjective f› ‹Surjective f› rfl rfl
  have hff₂ : UniversallyClosed ff :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹UniversallyClosed f›
      ‹UniversallyClosed f› rfl rfl

  have hsub : ff ⁻¹' Set.range (pullback.diagonal g) ⊆ Set.range R := by
    rintro w ⟨y, hy⟩
    obtain ⟨z, -, hz⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := pullback.diagonal g) (g := ff) y w hy
    exact ⟨sq.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, sq.isoPullback_inv_snd, hz]⟩
  have hrange : Set.range (pullback.diagonal g) = ff '' Set.range R := by
    apply subset_antisymm
    · rintro _ ⟨y, rfl⟩
      obtain ⟨w, hw⟩ := hff₁.surj (pullback.diagonal g y)
      obtain ⟨r, hr⟩ := hsub ⟨y, hw.symm⟩
      exact ⟨R r, ⟨r, rfl⟩, by rw [hr, hw]⟩
    · rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
      refine ⟨(pullback.fst f f ≫ f) r, ?_⟩
      change ((pullback.fst f f ≫ f) ≫ pullback.diagonal g) r = (R ≫ ff) r
      rw [sq.w]

  have hclosed : IsClosed (Set.range (pullback.diagonal g)) := by
    rw [hrange]
    exact ff.isClosedMap _ hRcl
  have : IsClosedImmersion (pullback.diagonal g) := .of_isPreimmersion _ hclosed
  exact ⟨‹_›⟩
