import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_UnramifiedWhittaker_summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow

set_option autoImplicit false

open Polynomial UnramifiedWhittaker

theorem UnramifiedWhittaker.summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow
    (N lam om lam' om' : ℂ) (hN : N ≠ 0) (y : ℂ)
    (hy : ‖y‖ * (max 1 (‖lam‖ + ‖N * om‖)) * (max 1 (‖lam'‖ + ‖N * om'‖)) < ‖N‖ ^ 2) :
    Summable fun m : ℕ =>
      heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m := by p2m_exact_reverting @_root_.P2MW.S_UnramifiedWhittaker_summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow.solution
