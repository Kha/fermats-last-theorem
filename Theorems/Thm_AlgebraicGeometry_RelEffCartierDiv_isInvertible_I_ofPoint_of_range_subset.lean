import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_ofPoint_of_range_subset

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_ofPoint_of_range_subset
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (V : C.Opens) [SmoothOfRelativeDimension 1 (V.ι ≫ c)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : T ⟶ C) (ha : a ≫ c = t)
    (hV : Set.range a.base ⊆ (V : Set C)) :
    (RelEffCartierDiv.ofPoint c a ha).I.IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_ofPoint_of_range_subset.solution
