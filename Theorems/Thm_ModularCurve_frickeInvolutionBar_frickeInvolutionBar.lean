module

public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_frickeInvolutionBar_frickeInvolutionBar

@[expose] public section

open ModularCurve
theorem ModularCurve.frickeInvolutionBar_frickeInvolutionBar (N : ℕ) [NeZero N] (y : ModularCurve.modularFunctionFieldBar N) : ModularCurve.frickeInvolutionBar N (ModularCurve.frickeInvolutionBar N y) = y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frickeInvolutionBar_frickeInvolutionBar.solution
