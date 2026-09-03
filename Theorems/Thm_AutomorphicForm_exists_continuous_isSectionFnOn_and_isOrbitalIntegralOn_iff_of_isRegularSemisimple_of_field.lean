import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_of_isRegularSemisimple_of_field

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_of_isRegularSemisimple_of_field
    (A : Type) [Field A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (μ : @Measure (GL (Fin 2) A) (glBorelOf A))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf A) μ)
    (γ : GL (Fin 2) A) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ)
    (f : GL (Fin 2) A → ℂ) (hfm : Measurable[glBorelOf A] f)
    (hfc : HasCompactSupport f) (hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) :
    (∃ w : GL (Fin 2) A → ℝ, IsSectionFnOn A γ τ f w ∧ Continuous w) ∧
      ∀ w : GL (Fin 2) A → ℝ, IsSectionFnOn A γ τ f w →
        ∀ I : ℂ, IsOrbitalIntegralOn A μ γ τ f I ↔
          I = @integral _ ℂ _ _ (glBorelOf A) μ fun x => f (x⁻¹ * γ * x) * (w x : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_of_isRegularSemisimple_of_field.solution
