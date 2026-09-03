import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) :
    ∃ (m : ℕ) (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
      (Ψ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (Fin (m + 1) → w.1.adicCompletion L)),
      (∀ z : L ⊗[K] v.adicCompletion K,
        (∀ k : Fin m, Ψ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) k.castSucc = Ψ z k.succ) ∧
          Ψ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) (Fin.last m) = θ (Ψ z 0)) ∧
      (∀ z : L ⊗[K] v.adicCompletion K,
        z ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ j, Ψ z j ∈ w.1.adicCompletionIntegers L) ∧
      (∀ (x : L) (j : Fin (m + 1)),
        Ψ (x ⊗ₜ[K] (1 : v.adicCompletion K)) j = algebraMap L (w.1.adicCompletion L) ((σ ^ (j : ℕ)) x)) ∧
      orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) ∧
      (∀ y : w.1.adicCompletion L,
        θ y = y ↔ y ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))) ∧
      (∀ y : w.1.adicCompletion L, Valued.v (θ y) = Valued.v y) ∧
      (m + 1) * Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L ∧
      Nat.card (v.Extension (𝓞 L)) = m + 1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers.solution
