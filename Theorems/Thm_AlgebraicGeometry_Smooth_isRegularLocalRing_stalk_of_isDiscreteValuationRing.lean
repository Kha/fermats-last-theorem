import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

universe u

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] (x : T) :
    IsRegularLocalRing (T.presheaf.stalk x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.solution
