import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_SplitPlace_exists_equiv_extension_algEquiv_forall_psi_eq_and_mem_adicCompletionIntegers_iff_and_norm_eq

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.SplitPlace.exists_equiv_extension_algEquiv_forall_psi_eq_and_mem_adicCompletionIntegers_iff_and_norm_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (ι : L →ₐ[K] v.adicCompletion K) :
    ∃ (e : Fin (Module.finrank K L) ≃ v.Extension (𝓞 L))
      (θ : ∀ i : Fin (Module.finrank K L), ((e i).1.adicCompletion L) ≃ₐ[v.adicCompletion K] v.adicCompletion K),
      (∀ (z : L ⊗[K] v.adicCompletion K) (i : Fin (Module.finrank K L)),
        AutomorphicForm.SplitPlace.psi K L (v.adicCompletion K) σ ι z i =
          θ i (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v z (e i))) ∧
      (∀ (i : Fin (Module.finrank K L)) (y : (e i).1.adicCompletion L),
        θ i y ∈ v.adicCompletionIntegers K ↔ y ∈ (e i).1.adicCompletionIntegers L) ∧
      (∀ (i : Fin (Module.finrank K L)) (y : (e i).1.adicCompletion L), ‖θ i y‖ = ‖y‖) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SplitPlace_exists_equiv_extension_algEquiv_forall_psi_eq_and_mem_adicCompletionIntegers_iff_and_norm_eq.solution
