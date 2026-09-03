import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    (∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (xa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
        (xv : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
        (∀ v ∉ S, xv v ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
        ∃ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          AutomorphicForm.tensorArch K L x = xa ∧
          ∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.tensorPlace K L v x = xv v) ∧
    (∀ x x' : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
        AutomorphicForm.tensorArch K L x = AutomorphicForm.tensorArch K L x' →
        (∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.tensorPlace K L v x = AutomorphicForm.tensorPlace K L v x') →
          x = x') := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext.solution
