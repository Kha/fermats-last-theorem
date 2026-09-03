import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_nhds_forall_mem_localCentralizer_isNormConjugator_mul_of_isNormConjugator_mul

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_forall_mem_localCentralizer_isNormConjugator_mul_of_isNormConjugator_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hu₀ : u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (y₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hy₀ : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ₀ (u₀ * δ) y₀) :
    ∀ V ∈ nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)),
        ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ →
          ∃ u ∈ V, u ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ∧
            u ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ∧
            AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ (u * δ)) ∧
            AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ (u * δ) y₀ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_nhds_forall_mem_localCentralizer_isNormConjugator_mul_of_isNormConjugator_mul.solution
