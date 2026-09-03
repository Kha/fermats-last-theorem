import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_norm_le_sum_mul_norm_of_isTwistedOrbitalIntegral_of_norm_le_sum_indicator
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

theorem AutomorphicForm.norm_le_sum_mul_norm_of_isTwistedOrbitalIntegral_of_norm_le_sum_indicator
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv)
    (ι : Type) (s : Finset ι) (U : ι → Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hUo : ∀ i ∈ s, IsOpen (U i)) (hUc : ∀ i ∈ s, IsCompact (U i))
    (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hle : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K), ‖φv g‖ ≤ ∑ i ∈ s, c i * (U i).indicator (fun _ => (1 : ℝ)) g)
    (I : ℂ) (hI : AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I)
    (J : ι → ℂ)
    (hJ : ∀ i ∈ s, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' ((U i).indicator (fun _ => (1 : ℂ))) (J i)) :
    ‖I‖ ≤ ∑ i ∈ s, c i * ‖J i‖ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_norm_le_sum_mul_norm_of_isTwistedOrbitalIntegral_of_norm_le_sum_indicator.solution
