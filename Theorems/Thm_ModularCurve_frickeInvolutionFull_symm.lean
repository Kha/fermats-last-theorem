import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_frickeInvolutionFull_symm

open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.frickeInvolutionFull_symm (N : ℕ) [NeZero N] : (frickeInvolutionFull N).symm = frickeInvolutionFull N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frickeInvolutionFull_symm.solution
