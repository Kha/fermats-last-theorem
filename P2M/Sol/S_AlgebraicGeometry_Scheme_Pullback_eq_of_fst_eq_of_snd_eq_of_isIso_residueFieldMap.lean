import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {t₁ t₂ : ↥(pullback f g)}
    (h₁ : (pullback.fst f g).base t₁ = (pullback.fst f g).base t₂)
    (h₂ : (pullback.snd f g).base t₁ = (pullback.snd f g).base t₂)
    [IsIso (f.residueFieldMap ((pullback.fst f g).base t₂))] :
    t₁ = t₂ := by
  apply Scheme.Pullback.carrierEquiv.injective
  refine Scheme.Pullback.carrierEquiv_eq_iff.mpr ⟨Scheme.Pullback.Triplet.ext h₁ h₂, ?_⟩

  set T := Scheme.Pullback.Triplet.ofPoint t₂ with hT
  haveI : IsIso ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) := by
    haveI : IsIso (f.residueFieldMap T.x) := inferInstanceAs (IsIso (f.residueFieldMap ((pullback.fst f g).base t₂)))
    infer_instance
  haveI hinr : IsIso (pushout.inr ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) :=
    pushout_inr_iso_of_left_iso _ _
  have hsub : Subsingleton ↥(Spec T.tensor) := by
    constructor
    intro a b
    exact (Spec.map (pushout.inr ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))).isOpenEmbedding.injective (Subsingleton.elim _ _)
  exact @Subsingleton.elim _ hsub _ _
