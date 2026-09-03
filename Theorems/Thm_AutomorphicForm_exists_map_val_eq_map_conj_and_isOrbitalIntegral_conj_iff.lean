import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ x : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)) :
    ∃ τ' : @Measure (AutomorphicForm.localCentralizer K v (x * γ * x⁻¹))
        (AutomorphicForm.localCentralizerBorel K v (x * γ * x⁻¹)),
      @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v (x * γ * x⁻¹)) (AutomorphicForm.localGLBorel K v)
          Subtype.val τ' =
        @Measure.map _ _ (AutomorphicForm.localGLBorel K v) (AutomorphicForm.localGLBorel K v)
          (fun g : GL (Fin 2) (v.adicCompletion K) => x * g * x⁻¹)
          (@Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
            Subtype.val τ) ∧
      (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (x * γ * x⁻¹)) τ') ∧
      ∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ),
        AutomorphicForm.IsOrbitalIntegral K v (x * γ * x⁻¹) τ' f I ↔
          AutomorphicForm.IsOrbitalIntegral K v γ τ f I := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff.solution
