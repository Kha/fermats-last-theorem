import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_frickeInvolutionFull_apply_apply
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
