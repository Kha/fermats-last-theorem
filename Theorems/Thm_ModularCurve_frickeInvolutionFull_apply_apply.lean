module

public import Definitions.Def_ModularCurve_AtkinLehner
public import P2M.Util
public import P2M.Sol.S_ModularCurve_frickeInvolutionFull_apply_apply

@[expose] public section

open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.frickeInvolutionFull_apply_apply (N : ℕ) [NeZero N] (x : modularFunctionFieldFull N) : frickeInvolutionFull N (frickeInvolutionFull N x) = x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frickeInvolutionFull_apply_apply.solution
