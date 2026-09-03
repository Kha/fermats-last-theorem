import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_RubinSilverberg_kleinCurve_Psi3_eval_ne_zero

open RubinSilverberg
theorem RubinSilverberg.kleinCurve_Psi3_eval_ne_zero {K : Type*} [Field K] [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) (x : RatFunc K) : ((kleinCurve (RatFunc.X : RatFunc K)).Ψ₃).eval x ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_kleinCurve_Psi3_eval_ne_zero.solution
