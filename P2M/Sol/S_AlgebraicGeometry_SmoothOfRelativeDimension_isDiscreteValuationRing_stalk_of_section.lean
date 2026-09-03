import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 f]
    (p : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    IsDiscreteValuationRing (X.presheaf.stalk (p.base (IsLocalRing.closedPoint k))) := by
  apply AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed f
  have : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id _ _ hp
  have h := p.isClosedEmbedding.isClosed_range
  have hr : Set.range p.base = {p.base (IsLocalRing.closedPoint k)} :=
    Set.range_eq_singleton_iff.mpr fun y => congrArg p.base (Subsingleton.elim _ _)
  rwa [hr] at h
