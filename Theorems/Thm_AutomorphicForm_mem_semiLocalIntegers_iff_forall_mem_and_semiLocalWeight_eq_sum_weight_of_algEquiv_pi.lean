import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι]
    (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (ι → v.adicCompletion K)) :
    (∀ x : L ⊗[K] v.adicCompletion K,
        x ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ i : ι, e x i ∈ v.adicCompletionIntegers K) ∧
    (∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.semiLocalWeight K L v g =
          ∑ i : ι, AutomorphicForm.LocalWeight.weight
            (Matrix.GeneralLinearGroup.map
              ((Pi.evalAlgHom (v.adicCompletion K) (fun _ : ι => v.adicCompletion K) i).comp
                e.toAlgHom).toRingHom g)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mem_semiLocalIntegers_iff_forall_mem_and_semiLocalWeight_eq_sum_weight_of_algEquiv_pi.solution
