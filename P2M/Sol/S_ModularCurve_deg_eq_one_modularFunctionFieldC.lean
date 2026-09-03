import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
namespace P2MW.S_ModularCurve_deg_eq_one_modularFunctionFieldC

open AlgebraicCurve ModularCurve

theorem solution
    (K : Type*) [Field K] (N : ℕ) [NeZero N] [IsAlgClosed K]
    [IsCurveOver K (modularFunctionFieldC K N)] :
    ∀ w : Place K (modularFunctionFieldC K N), w.deg = 1 :=
  IsCurveOver.forall_deg_eq_one_of_isAlgClosed
