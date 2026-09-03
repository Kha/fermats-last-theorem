import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple
    (K : Type) [Field K] [NumberField K] (v : NumberField.InfinitePlace K)
    (μ : @Measure (GL (Fin 2) v.Completion) (glBorelOf v.Completion))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf v.Completion) μ)
    (γ : GL (Fin 2) v.Completion) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) v.Completion))) (centralizerBorel v.Completion γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel v.Completion γ) τ)
    (f : GL (Fin 2) v.Completion → ℂ) (hfm : Measurable[glBorelOf v.Completion] f)
    (hfc : HasCompactSupport f) (hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) :
    (∃ w : GL (Fin 2) v.Completion → ℝ, IsSectionFnOn v.Completion γ τ f w ∧ Continuous w) ∧
      ∀ w : GL (Fin 2) v.Completion → ℝ, IsSectionFnOn v.Completion γ τ f w →
        ∀ I : ℂ, IsOrbitalIntegralOn v.Completion μ γ τ f I ↔
          I = @integral _ ℂ _ _ (glBorelOf v.Completion) μ fun x => f (x⁻¹ * γ * x) * (w x : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_completion_of_isRegularSemisimple.solution
