import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval

set_option autoImplicit false

open Polynomial UnramifiedWhittaker

theorem UnramifiedWhittaker.tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval
    (N lam om lam' om' : ℂ) (hN : N ≠ 0) (y : ℂ)
    (hsum : Summable fun m : ℕ =>
      heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m) :
    (∑' m : ℕ, heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m) *
        (LanglandsTunnell.RankinSelberg.rsEulerPoly lam (N * om) lam' (N * om') 0).eval (y / N ^ 2) =
      1 - om * om' * (y / N) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval.solution
