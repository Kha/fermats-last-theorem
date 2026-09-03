import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem solution
    {σ : Type u} (X : σ → Scheme.{u}) {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    (hf : ∀ i, IsSeparated (f i)) : IsSeparated (Sigma.desc f) := by

  constructor
  refine IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeftRight (sigmaOpenCover X) (sigmaOpenCover X) (Sigma.desc f) (Sigma.desc f)) ?_
  rintro ⟨i, j⟩
  have H := pullback_map_diagonal_isPullback (Sigma.ι X i) (Sigma.ι X j) (Sigma.desc f)
  show IsClosedImmersion (pullback.snd (pullback.diagonal (Sigma.desc f))
    (pullback.map (Sigma.ι X i ≫ Sigma.desc f) (Sigma.ι X j ≫ Sigma.desc f) (Sigma.desc f) (Sigma.desc f)
      (Sigma.ι X i) (Sigma.ι X j) (𝟙 _) (Category.comp_id _) (Category.comp_id _)))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion H.isoPullback.hom, IsPullback.isoPullback_hom_snd]
  by_cases hij : i = j
  · subst hij
    have hfi : Sigma.ι X i ≫ Sigma.desc f = f i := Sigma.ι_desc _ _
    haveI : IsSeparated (Sigma.ι X i ≫ Sigma.desc f) := by rw [hfi]; exact hf i
    haveI : IsClosedImmersion
        (pullback.fst (Sigma.ι X i) (Sigma.ι X i) ≫ pullback.diagonal (Sigma.ι X i ≫ Sigma.desc f)) :=
      inferInstance
    convert this using 2
    apply pullback.hom_ext <;> simp [fst_eq_snd_of_mono_eq]
  · haveI : IsEmpty ↑(pullback (Sigma.ι X i) (Sigma.ι X j)) := isEmpty_pullback_sigmaι_of_ne X hij
    infer_instance
