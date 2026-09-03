import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_RubinSilverberg_rsMember_Psi3_eval_ne_zero

open RubinSilverberg
theorem RubinSilverberg.rsMember_Psi3_eval_ne_zero {K : Type*} [Field K] [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) {a b u₀ : K} (ha : a ≠ 0) (hb : b ≠ 0) (hu₀ : IsKleinDatum a b u₀) (l : K) (x : RatFunc K) : ((rsMember (RatFunc.C a) (RatFunc.C b) (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : RatFunc K)).Ψ₃).eval x ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_rsMember_Psi3_eval_ne_zero.solution
