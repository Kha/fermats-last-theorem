module

public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_isCusp_cuspZeroBar

@[expose] public section

open ModularCurve AlgebraicCurve

theorem ModularCurve.isCusp_cuspZeroBar (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (cuspZeroBar N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isCusp_cuspZeroBar.solution
