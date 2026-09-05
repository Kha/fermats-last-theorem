module

public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Sol.S_ModularCurve_isCusp_iff_ord_neg
import P2M.Sol.S_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
import P2M.Util

namespace P2MW.S_ModularCurve_isCusp_cuspZeroBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) :
    IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (cuspZeroBar N) := by
  rw [ModularCurve.isCusp_iff_ord_neg, ModularCurve.ord_cuspZeroBar_coeffEmb_jq N h, neg_lt_zero, Nat.cast_pos]
  exact Nat.pos_of_ne_zero (NeZero.ne N)
end S_ModularCurve_isCusp_cuspZeroBar
end P2MW

public section
open ModularCurve AlgebraicCurve

theorem ModularCurve.isCusp_cuspZeroBar (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (cuspZeroBar N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isCusp_cuspZeroBar.solution
end
