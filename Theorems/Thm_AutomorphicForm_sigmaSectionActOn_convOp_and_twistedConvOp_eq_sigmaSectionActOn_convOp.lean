import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_sigmaSectionActOn_convOp_and_twistedConvOp_eq_sigmaSectionActOn_convOp
attribute [-simp] FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.sigmaSectionActOn_convOp_and_twistedConvOp_eq_sigmaSectionActOn_convOp
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (f u : AdelicGL2 (𝓞 L) L → ℂ) :
    sigmaSectionActOn K L D σ (convOp L f u) =
      convOp L (sigmaSectionActOn K L D σ f) (sigmaSectionActOn K L D σ u) ∧
    twistedConvOp K L D σ f u =
      sigmaSectionActOn K L D σ (convOp L (sigmaSectionActOn K L D σ⁻¹ f) u) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_sigmaSectionActOn_convOp_and_twistedConvOp_eq_sigmaSectionActOn_convOp.solution
