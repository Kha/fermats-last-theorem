import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isIso_morphismRestrict_and_smoothOfRelativeDimension_one_of_coe_eq_compl_range_of_isClosedImmersion
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem solution
    {k : Type u} [Field k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 c₁]
    (i₁ : SchemeHomOver c₁ x) (i₂ : C₂ ⟶ X) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.base)
    (U : X.Opens) (hU : (U : Set X) = (Set.range i₂.base)ᶜ) :
    IsIso (i₁.1 ∣_ U) ∧ SmoothOfRelativeDimension 1 (U.ι ≫ x) := by
  obtain ⟨i, hi⟩ := i₁
  subst hi

  haveI : Surjective (i ∣_ U) := by
    refine ⟨fun u => ?_⟩
    rcases hjs u.1 with ⟨z, hz⟩ | ⟨z, hz⟩
    · have hzU : z ∈ i ⁻¹ᵁ U := by
        change i.base z ∈ U
        rw [hz]; exact u.2
      refine ⟨⟨z, hzU⟩, Subtype.ext ?_⟩
      rw [morphismRestrict_base_coe]
      exact hz
    · exfalso
      have hu : (u.1 : X) ∈ (U : Set X) := u.2
      rw [hU] at hu
      exact hu ⟨z, hz⟩
  haveI : IsReduced (U : Scheme.{u}) := isReduced_of_isOpenImmersion U.ι
  have hiso : IsIso (i ∣_ U) := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨hiso, ?_⟩

  have hfac : U.ι ≫ x = inv (i ∣_ U) ≫ ((i ⁻¹ᵁ U).ι ≫ i ≫ x) := by
    rw [← Category.assoc (i ⁻¹ᵁ U).ι i x, ← morphismRestrict_ι, Category.assoc, IsIso.inv_hom_id_assoc]
  have h01 : SmoothOfRelativeDimension (0 + 1) ((i ⁻¹ᵁ U).ι ≫ i ≫ x) := inferInstance
  haveI h1 : SmoothOfRelativeDimension 1 ((i ⁻¹ᵁ U).ι ≫ i ≫ x) := by simpa using h01
  have h : SmoothOfRelativeDimension (0 + 1) (inv (i ∣_ U) ≫ ((i ⁻¹ᵁ U).ι ≫ i ≫ x)) := inferInstance
  rw [hfac]
  simpa using h
