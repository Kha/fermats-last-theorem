import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_IsCurveOver_trdeg_eq_one

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.IsCurveOver.trdeg_eq_one
    (K F : Type*) [Field K] [Field F] [Algebra K F] [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    Algebra.trdeg K F = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_IsCurveOver_trdeg_eq_one.solution
