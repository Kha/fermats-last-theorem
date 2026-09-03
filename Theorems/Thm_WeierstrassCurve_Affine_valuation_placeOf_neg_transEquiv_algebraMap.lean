import Mathlib
import Definitions.Def_EllipticCurve_FunctionFieldPullback
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_valuation_placeOf_neg_transEquiv_algebraMap

open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.Affine.valuation_placeOf_neg_transEquiv_algebraMap {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] (S : (W⁄K).Point) (hS : S ≠ 0) {a : (W⁄K).CoordinateRing} (ha : a ≠ 0) : (placeOf W K (-S) (neg_ne_zero.mpr hS)).valuation (W⁄K).FunctionField (transEquiv W K S (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField a)) = WithZero.exp ((Algebra.norm (Polynomial K) a).natDegree : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_valuation_placeOf_neg_transEquiv_algebraMap.solution
