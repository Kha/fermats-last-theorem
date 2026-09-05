module

public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Sol.S_ModularCurve_frickeInvolutionFull_symm
import P2M.Util

namespace P2MW.S_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
open ModularCurve

theorem solution (N : ℕ) [NeZero N] (y : ModularCurve.modularFunctionFieldBar N) : ModularCurve.frickeInvolutionBar N (ModularCurve.frickeInvolutionBar N y) = y := by
  have hfix : ∀ z, frickeInvolutionFull N (frickeInvolutionFull N z) = z := fun z => by
    nth_rewrite 1 [← frickeInvolutionFull_symm N]
    exact AlgEquiv.symm_apply_apply _ _
  have hsq : frickeInvolutionFull N * frickeInvolutionFull N = 1 := AlgEquiv.ext fun z => by
    rw [AlgEquiv.mul_apply, hfix, AlgEquiv.one_apply]
  rw [frickeInvolutionBar_def, ← AlgEquiv.mul_apply, ← map_mul, hsq, map_one, AlgEquiv.one_apply]
end S_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
end P2MW

public section
open ModularCurve
theorem ModularCurve.frickeInvolutionBar_frickeInvolutionBar (N : ℕ) [NeZero N] (y : ModularCurve.modularFunctionFieldBar N) : ModularCurve.frickeInvolutionBar N (ModularCurve.frickeInvolutionBar N y) = y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frickeInvolutionBar_frickeInvolutionBar.solution
end
