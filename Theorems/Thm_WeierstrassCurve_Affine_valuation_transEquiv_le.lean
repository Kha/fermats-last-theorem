import Mathlib
import Definitions.Def_EllipticCurve_FunctionFieldPullback
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_valuation_transEquiv_le

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
theorem WeierstrassCurve.Affine.valuation_transEquiv_le {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K] [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {P S : (W⁄K).Point} (hP : P ≠ 0) (hS : S ≠ 0) (hx : P.xc ≠ S.xc) (hPS : P + S ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ) (hh : (placeOf W K (P + S) hPS).valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) : (placeOf W K P hP).valuation (W⁄K).FunctionField (transEquiv W K S h) ≤ exp (-(k : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_valuation_transEquiv_le.solution
