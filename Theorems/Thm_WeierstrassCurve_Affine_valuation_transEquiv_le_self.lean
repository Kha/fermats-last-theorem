import Mathlib
import Definitions.Def_EllipticCurve_FunctionFieldPullback
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_valuation_transEquiv_le_self

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
theorem WeierstrassCurve.Affine.valuation_transEquiv_le_self {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K] [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {S : (W⁄K).Point} (hS : S ≠ 0) (h2S : S + S ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ) (hh : (placeOf W K (S + S) h2S).valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) : (placeOf W K S hS).valuation (W⁄K).FunctionField (transEquiv W K S h) ≤ exp (-(k : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_valuation_transEquiv_le_self.solution
