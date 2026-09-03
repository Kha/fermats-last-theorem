import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import P2M.Util
import P2M.Sol.S_RubinSilverberg_kleinCurve_prePsi_five_eval_kleinX

open RubinSilverberg
theorem RubinSilverberg.kleinCurve_prePsi_five_eval_kleinX {K : Type*} [Field K] [CharZero K] (u : K) : ((kleinCurve u).preΨ' 5).eval (kleinX u) = 0 := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_kleinCurve_prePsi_five_eval_kleinX.solution
