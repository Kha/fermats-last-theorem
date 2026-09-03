import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi

set_option autoImplicit false

open NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
    (hΞ : Continuous Ξ) (hΞ' : Continuous Ξ.symm)
    (hΞt : ∀ (x : L) (a : InfiniteAdeleRing K) (v : InfinitePlace K), Ξ (x ⊗ₜ a) v = x ⊗ₜ (a v)) :
    ∃ Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)),
      Continuous Θ ∧ Continuous Θ.symm ∧
      (∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ g v = Matrix.GeneralLinearGroup.map
          ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g) ∧
      (∀ (σ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v)) ∧
      (∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ (toTensorGL K L (InfiniteAdeleRing K) g) v =
          toTensorGL K L v.Completion
            (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) v) g)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi.solution
