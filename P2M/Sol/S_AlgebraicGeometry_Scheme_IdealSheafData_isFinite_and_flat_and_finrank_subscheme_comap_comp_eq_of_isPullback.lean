import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_flat_and_finrank_subscheme_comap_comp_eq_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (y : Y ⟶ T) (bc : Y ⟶ X)
    (H : IsPullback bc y f g) [IsLocallyNoetherian S] [PreconnectedSpace S]
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)] :
    IsFinite ((I.comap bc).subschemeι ≫ y) ∧ Flat ((I.comap bc).subschemeι ≫ y) ∧
      ∀ (t : T) (s : S), ((I.comap bc).subschemeι ≫ y).finrank t = (I.subschemeι ≫ f).finrank s := by

  have sq : IsPullback (pullback.snd bc I.subschemeι) (pullback.fst bc I.subschemeι ≫ y) (I.subschemeι ≫ f) g :=
    (IsPullback.of_hasPullback bc I.subschemeι).flip.paste_vert H
  have hfin' : IsFinite (pullback.fst bc I.subschemeι ≫ y) :=
    MorphismProperty.of_isPullback sq inferInstance
  have hflat' : Flat (pullback.fst bc I.subschemeι ≫ y) :=
    MorphismProperty.of_isPullback sq inferInstance
  have he : (I.comap bc).subschemeι ≫ y = (I.comapIso bc).hom ≫ (pullback.fst bc I.subschemeι ≫ y) := by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  refine ⟨?_, ?_, fun t s => ?_⟩
  · rw [he]; infer_instance
  · rw [he]; infer_instance
  · have hlfp : LocallyOfFinitePresentation (I.subschemeι ≫ f) := inferInstance
    have hconst := (Scheme.Hom.isLocallyConstant_finrank (I.subschemeι ≫ f)).apply_eq_of_preconnectedSpace
      (g.base t) s
    rw [he, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ sq t]
    exact hconst
