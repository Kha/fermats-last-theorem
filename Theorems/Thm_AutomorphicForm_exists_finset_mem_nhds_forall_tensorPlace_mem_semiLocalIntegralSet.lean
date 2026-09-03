import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x₀ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∃ U ∈ nhds x₀,
      ∀ x ∈ U, ∀ v ∉ S₀, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet.solution
