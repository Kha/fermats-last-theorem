import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (x : C) (hx : x ≠ genericPoint C) : IsClosed ({x} : Set C) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint.solution
