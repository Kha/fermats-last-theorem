import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand
import P2M.Util
namespace P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_jqN

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) :
    (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ = -1 := by
  have e := ModularCurve.ord_cuspZeroBar_coeffEmb_qExpand N h 1 N (one_mul N)
  rw [Nat.cast_one] at e
  exact e
