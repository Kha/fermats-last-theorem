module

public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Sol.S_ModularCurve_frickeInvolutionFull_apply_apply
import P2M.Util

namespace P2MW.S_ModularCurve_frickeInvolutionFull_symm

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField

noncomputable section

theorem solution (N : ℕ) [NeZero N] : (frickeInvolutionFull N).symm = frickeInvolutionFull N := by
  apply AlgEquiv.ext
  intro x
  rw [AlgEquiv.symm_apply_eq, ModularCurve.frickeInvolutionFull_apply_apply]

end
end S_ModularCurve_frickeInvolutionFull_symm
end P2MW

public section
open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.frickeInvolutionFull_symm (N : ℕ) [NeZero N] : (frickeInvolutionFull N).symm = frickeInvolutionFull N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frickeInvolutionFull_symm.solution
end
