import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hx : s ≫ t = x) :
    ∃ φ : pullback (pullback.snd c t) s ≅ pullback c x,
      φ.hom ≫ pullback.snd c x = fibreAt c t s ∧
      φ.hom ≫ pullback.fst c x = pullback.fst (pullback.snd c t) s ≫ pullback.fst c t ∧
      φ.hom ≫ baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t) = pullback.fst (pullback.snd c t) s := by

  subst hx
  refine ⟨pullbackLeftPullbackSndIso c t s, ?_, ?_, ?_⟩
  · simp [fibreAt]
  · simp
  · apply pullback.hom_ext
    · simp only [baseChangeSnd, Category.assoc, pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
    · simp only [baseChangeSnd, Category.assoc, pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]
