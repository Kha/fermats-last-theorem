import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_IsFrickeAutFull_eq_frickeInvolutionFull

open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.IsFrickeAutFull.eq_frickeInvolutionFull {N : ℕ} [NeZero N] {σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N} (hσ : IsFrickeAutFull N σ) : σ = frickeInvolutionFull N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsFrickeAutFull_eq_frickeInvolutionFull.solution
