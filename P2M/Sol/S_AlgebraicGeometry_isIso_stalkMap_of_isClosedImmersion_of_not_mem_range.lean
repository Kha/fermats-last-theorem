import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isIso_stalkMap_of_isClosedImmersion_of_not_mem_range

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace ResidueOrdAux

theorem isIso_of_isClosedImmersion_of_surjective_of_isReduced {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [IsClosedImmersion f] [IsReduced Y] (hf : Function.Surjective f.base) : IsIso f := by
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot, ← le_bot_iff, ← Scheme.nilradical_eq_bot (X := Y),
    ← Scheme.IdealSheafData.vanishingIdeal_top, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  have h : ((f.ker).support : Set Y) = Set.univ := by
    rw [Scheme.Hom.support_ker, Set.range_eq_univ.mpr hf, closure_univ]
  intro z _
  show z ∈ ((f.ker).support : Set Y)
  rw [h]; trivial

theorem isIso_stalkMap_of_isClosedImmersion_of_not_mem_range {Z M₁ M₂ : Scheme.{u}} [IsReduced Z]
    (i₁ : M₁ ⟶ Z) (i₂ : M₂ ⟶ Z) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : ∀ z : Z, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (y : M₁) (hy : i₁.base y ∉ Set.range i₂.base) : IsIso (i₁.stalkMap y) := by
  let Ω : Z.Opens := ⟨(Set.range i₂.base)ᶜ, (IsClosedImmersion.isClosedEmbedding i₂).isClosed_range.isOpen_compl⟩
  haveI : IsReduced (Ω : Scheme.{u}) := isReduced_of_isOpenImmersion Ω.ι
  have hf : Function.Surjective (pullback.snd i₁ Ω.ι).base := by
    intro z
    have hz : Ω.ι.base z ∈ Set.range i₁.base := by
      rcases hcover (Ω.ι.base z) with h | h
      · exact h
      · exact absurd h z.2
    obtain ⟨m, hm⟩ := hz
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback m z hm
    exact ⟨w, hw⟩
  haveI : IsIso (pullback.snd i₁ Ω.ι) := isIso_of_isClosedImmersion_of_surjective_of_isReduced _ hf

  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := Ω.ι) y ⟨i₁.base y, hy⟩ rfl
  subst hw
  haveI hs : IsIso ((pullback.snd i₁ Ω.ι).stalkMap w) := inferInstance
  haveI hΩι : IsOpenImmersion Ω.ι := inferInstance
  haveI hΩ : IsIso (Ω.ι.stalkMap ((pullback.snd i₁ Ω.ι).base w)) :=
    inferInstanceAs (IsIso (Ω.ι.toLRSHom.stalkMap ((pullback.snd i₁ Ω.ι).base w)))
  have h1 : IsIso ((pullback.fst i₁ Ω.ι ≫ i₁).stalkMap w) := by
    rw [pullback.condition, Scheme.Hom.stalkMap_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ (Ω.ι.stalkMap ((pullback.snd i₁ Ω.ι).base w))
      ((pullback.snd i₁ Ω.ι).stalkMap w) hΩ hs
  rw [Scheme.Hom.stalkMap_comp] at h1
  haveI hf : IsIso ((pullback.fst i₁ Ω.ι).stalkMap w) := inferInstance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (i₁.stalkMap ((pullback.fst i₁ Ω.ι).base w))
    ((pullback.fst i₁ Ω.ι).stalkMap w) hf h1

end ResidueOrdAux

theorem solution
    {Z M₁ M₂ : Scheme.{u}} [IsReduced Z]
    (i₁ : M₁ ⟶ Z) (i₂ : M₂ ⟶ Z) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : ∀ z : Z, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (y : M₁) (hy : i₁.base y ∉ Set.range i₂.base) :
    IsIso (i₁.stalkMap y) :=
  ResidueOrdAux.isIso_stalkMap_of_isClosedImmersion_of_not_mem_range i₁ i₂ hcover y hy
