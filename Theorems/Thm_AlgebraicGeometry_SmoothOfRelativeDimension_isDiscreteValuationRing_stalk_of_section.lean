import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section

universe u v

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_section
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 f]
    (p : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    IsDiscreteValuationRing (X.presheaf.stalk (p.base (IsLocalRing.closedPoint k))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section.solution
