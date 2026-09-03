import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isCompact_and_exists_isOpen_conj_integralOrder_twistedCommutant_of_map_conj_eq_smul_map_toTensorGL_localHaar

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal Topology

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.isCompact_and_exists_isOpen_conj_integralOrder_twistedCommutant_of_map_conj_eq_smul_map_toTensorGL_localHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) (hτ'h : τ'.IsHaarMeasure)
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (tv : ℝ≥0∞)
    (hτ' : (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) τ' =
          tv • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)))
    (Λ : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hΛ : Λ = {x | x * ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
              x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)} ∩
      {x | ∃ m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, m i j ∈ v.adicCompletionIntegers K) ∧
        ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * x *
          ((y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          m.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K)}) :
    IsCompact Λ ∧
    (∃ V : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)), IsOpen V ∧ Λ = V ∩ {x | x * ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
              x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)}) ∧
    (∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ Λ ↔
        ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ {x | x * ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
              x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)} ∧
          ∃ g : GL (Fin 2) (v.adicCompletion K),
            (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
            y⁻¹ * x * y = AutomorphicForm.toTensorGL K L (v.adicCompletion K) g)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isCompact_and_exists_isOpen_conj_integralOrder_twistedCommutant_of_map_conj_eq_smul_map_toTensorGL_localHaar.solution
