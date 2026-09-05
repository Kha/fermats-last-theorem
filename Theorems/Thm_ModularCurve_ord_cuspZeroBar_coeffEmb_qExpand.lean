module

public import Definitions.Def_ModularCurve_CuspidalClass
public import P2M.Util
public import P2M.Sol.S_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand

@[expose] public section

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspZeroBar_coeffEmb_qExpand (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (a b : ℕ) (hab : a * b = N) [NeZero a] [NeZero b] : (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro_left a hab))⟩ = -a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand.solution
