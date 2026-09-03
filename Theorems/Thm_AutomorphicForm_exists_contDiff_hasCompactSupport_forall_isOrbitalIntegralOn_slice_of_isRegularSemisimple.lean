import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_isOrbitalIntegralOn_slice_of_isRegularSemisimple

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isOrbitalIntegralOn_slice_of_isRegularSemisimple
    (𝕜 : Type) [RCLike 𝕜] (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (μ : @Measure (GL (Fin 2) 𝕜) (glBorelOf 𝕜)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf 𝕜) μ)
    (γ : GL (Fin 2) 𝕜) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) 𝕜))) (centralizerBorel 𝕜 γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel 𝕜 γ) τ)
    (Φ : (Fin 2 → Fin 2 → 𝕜) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ∃ g : P → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      ∀ p : P,
        IsOrbitalIntegralOn 𝕜 μ γ τ (fun x => Φ (Matrix.of.symm (x : Matrix (Fin 2) (Fin 2) 𝕜), p)) (g p) ∧
        ∀ I : ℂ, IsOrbitalIntegralOn 𝕜 μ γ τ (fun x => Φ (Matrix.of.symm (x : Matrix (Fin 2) (Fin 2) 𝕜), p)) I →
          I = g p := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_isOrbitalIntegralOn_slice_of_isRegularSemisimple.solution
