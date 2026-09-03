import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : Finset (HeightOneSpectrum (𝓞 K)))
    (xa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (xv : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ∃ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.tensorArch K L x = xa ∧
      (∀ v ∈ B, AutomorphicForm.tensorPlace K L v x = xv v) ∧
      (∀ v ∉ B, AutomorphicForm.tensorPlace K L v x = 1) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_finset.solution
