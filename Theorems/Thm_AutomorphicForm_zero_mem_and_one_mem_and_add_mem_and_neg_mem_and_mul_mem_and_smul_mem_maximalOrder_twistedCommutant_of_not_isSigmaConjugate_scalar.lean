import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_TwistedCommutant
import P2M.Util
import P2M.Sol.S_AutomorphicForm_zero_mem_and_one_mem_and_add_mem_and_neg_mem_and_mul_mem_and_smul_mem_maximalOrder_twistedCommutant_of_not_isSigmaConjugate_scalar

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal Topology

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.zero_mem_and_one_mem_and_add_mem_and_neg_mem_and_mul_mem_and_smul_mem_maximalOrder_twistedCommutant_of_not_isSigmaConjugate_scalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (O : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hO : O = {x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) | x * ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ∧
          (x = 0 ∨ ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) ≤ 1 ∧ Matrix.det x = (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) (s : v.adicCompletion K))}) :
    (0 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ O ∧ (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ O ∧
    (∀ x ∈ O, ∀ y ∈ O, x + y ∈ O) ∧ (∀ x ∈ O, -x ∈ O) ∧
    (∀ x ∈ O, ∀ y ∈ O, x * y ∈ O) ∧
    (∀ a : v.adicCompletion K, a ∈ v.adicCompletionIntegers K → ∀ x ∈ O, (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) a • x ∈ O) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_zero_mem_and_one_mem_and_add_mem_and_neg_mem_and_mul_mem_and_smul_mem_maximalOrder_twistedCommutant_of_not_isSigmaConjugate_scalar.solution
