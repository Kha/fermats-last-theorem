import Mathlib
import Theorems.Thm_AlgebraicGeometry_surjective_of_closedPoints_subset_range
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_surjective_of_forall_exists_comp_eq_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (h : ∀ y : Spec (CommRingCat.of K) ⟶ Y, y ≫ g = 𝟙 _ →
      ∃ x : Spec (CommRingCat.of K) ⟶ X, x ≫ f = y) :
    Surjective f := by
  have hJ : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace g
  have hN : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have hfp : LocallyOfFinitePresentation f := inferInstance
  refine AlgebraicGeometry.surjective_of_closedPoints_subset_range f fun y hy => ?_
  obtain ⟨x, hx⟩ := h (pointOfClosedPoint g y hy) (pointOfClosedPoint_comp g y hy)
  refine ⟨x.base (IsLocalRing.closedPoint K), ?_⟩
  have := congrArg (fun φ : Spec (CommRingCat.of K) ⟶ Y => φ.base (IsLocalRing.closedPoint K)) hx
  simpa [pointOfClosedPoint_apply] using this
