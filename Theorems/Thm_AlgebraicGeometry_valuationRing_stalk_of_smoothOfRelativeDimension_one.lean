import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.valuationRing_stalk_of_smoothOfRelativeDimension_one
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] (x : C) :
    ValuationRing (C.presheaf.stalk x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one.solution
