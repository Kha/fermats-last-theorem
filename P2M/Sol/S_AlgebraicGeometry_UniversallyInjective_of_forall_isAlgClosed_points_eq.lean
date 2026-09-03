import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_UniversallyInjective_of_forall_isAlgClosed_points_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x y : Spec (CommRingCat.of K) ⟶ X),
      x ≫ f = y ≫ f → x = y) :
    UniversallyInjective f := by
  rw [UniversallyInjective.iff_diagonal]
  refine ⟨fun t => ?_⟩

  let K : Type u := AlgebraicClosure ((pullback f f).residueField t)
  let ι : Spec (CommRingCat.of K) ⟶ pullback f f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback f f).residueField t) K)) ≫
      (pullback f f).fromSpecResidueField t
  have hfs : (ι ≫ pullback.fst f f) ≫ f = (ι ≫ pullback.snd f f) ≫ f := by
    simp only [Category.assoc, pullback.condition]

  have heq : ι ≫ pullback.fst f f = ι ≫ pullback.snd f f :=
    h K (ι ≫ pullback.fst f f) (ι ≫ pullback.snd f f) hfs

  have hι : (ι ≫ pullback.fst f f) ≫ pullback.diagonal f = ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, heq]
  refine ⟨(ι ≫ pullback.fst f f).base (IsLocalRing.closedPoint K), ?_⟩
  rw [← Scheme.Hom.comp_apply, hι, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply t _
