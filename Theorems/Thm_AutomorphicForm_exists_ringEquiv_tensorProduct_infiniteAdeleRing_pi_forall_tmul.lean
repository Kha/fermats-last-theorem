import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion),
      Continuous Ξ ∧ Continuous Ξ.symm ∧
      ∀ (x : L) (a : InfiniteAdeleRing K) (v : InfinitePlace K), Ξ (x ⊗ₜ a) v = x ⊗ₜ (a v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul.solution
