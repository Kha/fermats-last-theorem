module

public import Definitions.Def_ModularCurve_CuspidalClass
public import P2M.Util
public import P2M.Sol.S_ModularCurve_cuspZeroBar_ne_cuspInftyBar

@[expose] public section

open ModularCurve AlgebraicCurve

theorem ModularCurve.cuspZeroBar_ne_cuspInftyBar (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (hN : 1 < N) : cuspZeroBar N ≠ cuspInftyBar N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_cuspZeroBar_ne_cuspInftyBar.solution
