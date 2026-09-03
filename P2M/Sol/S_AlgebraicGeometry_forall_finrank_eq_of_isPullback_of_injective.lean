import Mathlib
import Theorems.Thm_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_forall_finrank_eq_of_isPullback_of_injective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R₀ L : Type} [CommRing R₀] [CommRing L] (φ : R₀ →+* L) (hφ : Function.Injective φ)
    {C₀ : Scheme.{0}} (h₀ : C₀ ⟶ Spec (CommRingCat.of R₀)) (hfin : IsFinite h₀) (hfl : Flat h₀)
    (hlfp : LocallyOfFinitePresentation h₀)
    {C : Scheme.{0}} (h : C ⟶ Spec (CommRingCat.of L)) (g : C ⟶ C₀)
    (hg : IsPullback g h h₀ (Spec.map (CommRingCat.ofHom φ)))
    (r : ℕ) (hrank : ∀ x : ↥(Spec (CommRingCat.of L)), h.finrank x = r)
    (t : ↥(Spec (CommRingCat.of R₀))) : h₀.finrank t = r := by
  haveI := hfl
  haveI := hfin
  haveI := hlfp
  have hW : IsClopen {t : ↥(Spec (CommRingCat.of R₀)) | h₀.finrank t = r} :=
    (Scheme.Hom.isLocallyConstant_finrank h₀).isClopen_fiber r
  have hWL : Set.range (Spec.map (CommRingCat.ofHom φ)).base ⊆ {t : ↥(Spec (CommRingCat.of R₀)) | h₀.finrank t = r} := by
    rintro _ ⟨x, rfl⟩
    show h₀.finrank ((Spec.map (CommRingCat.ofHom φ)).base x) = r
    rw [← Scheme.Hom.finrank_of_isPullback g h h₀ (Spec.map (CommRingCat.ofHom φ)) hg x]
    exact hrank x
  have := AlgebraicGeometry.eq_univ_of_isClopen_of_range_specMap_subset_of_injective φ hφ _ hW hWL
  have ht : t ∈ {t : ↥(Spec (CommRingCat.of R₀)) | h₀.finrank t = r} := by rw [this]; trivial
  exact ht
