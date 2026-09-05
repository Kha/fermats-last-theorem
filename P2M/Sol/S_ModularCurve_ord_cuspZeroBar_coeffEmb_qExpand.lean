module

public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Sol.S_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import P2M.Sol.S_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
import P2M.Util

namespace P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (a b : ℕ) (hab : a * b = N) [NeZero a] [NeZero b] :
    (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro_left a hab))⟩ = -a := by
  rw [cuspZeroBar_def, ← ModularCurve.frickeInvolutionBar_coeffEmb_qExpand N h a b hab, Place.ord_smul]
  exact ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand N a (Dvd.intro b hab)
end S_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand
end P2MW

public section
open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspZeroBar_coeffEmb_qExpand (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (a b : ℕ) (hab : a * b = N) [NeZero a] [NeZero b] : (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro_left a hab))⟩ = -a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand.solution
end
