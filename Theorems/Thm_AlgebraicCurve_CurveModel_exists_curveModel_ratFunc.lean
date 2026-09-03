import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_exists_curveModel_ratFunc

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

theorem AlgebraicCurve.CurveModel.exists_curveModel_ratFunc
    (κ : Type u) [Field κ] [IsAlgClosed κ] [Fact ((RatFunc.X : RatFunc κ) ≠ 0)] :
    ∃ (M : CurveModel κ (RatFunc κ)) (e : M.C ≅ CurveModel.glued κ (RatFunc.X : RatFunc κ)),
      e.hom ≫ CurveModel.gluedToBase κ (RatFunc.X : RatFunc κ) = M.toBase := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_exists_curveModel_ratFunc.solution
