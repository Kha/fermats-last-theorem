import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isCompact_and_exists_isOpen_maximalOrder_twistedCommutant_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal Topology

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.isCompact_and_exists_isOpen_maximalOrder_twistedCommutant_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (O : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hO : O = {x | x * ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
              x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ∧
          (x = 0 ∨ ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) ≤ 1 ∧
            Matrix.det x = (Algebra.TensorProduct.includeRight :
              v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) (s : v.adicCompletion K))}) :
    IsCompact O ∧
    (∃ V : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)), IsOpen V ∧
        O = V ∩ {x | x * ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
              x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)}) ∧
    (∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ O ↔
        ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ {x | x * ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
              x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)} ∧
          x ∈ ⋃ n : ℕ, {x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) | ∃ s : (v.adicCompletion K)ˣ,
              Valued.v (s : v.adicCompletion K) = WithZero.exp (-(n : ℤ)) ∧
              Matrix.GeneralLinearGroup.det x =
                Units.map (Algebra.TensorProduct.includeRight :
                  v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s})) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isCompact_and_exists_isOpen_maximalOrder_twistedCommutant_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.solution
