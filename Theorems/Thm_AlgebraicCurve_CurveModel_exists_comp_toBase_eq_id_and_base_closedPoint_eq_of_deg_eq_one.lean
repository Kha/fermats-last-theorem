import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (x : closedPoints M.C) (hx : (M.placeOfPoint x).deg = 1) :
    ∃ pt : Spec (CommRingCat.of K) ⟶ M.C,
      pt ≫ M.toBase = 𝟙 _ ∧ pt.base (IsLocalRing.closedPoint K) = x.1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one.solution
