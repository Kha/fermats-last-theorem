import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsOrbitalIntegralOn_unique_of_isRegularSemisimple

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.IsOrbitalIntegralOn.unique_of_isRegularSemisimple
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (μ : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μ)
    (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel A γ) τ)
    (f : GL (Fin 2) A → ℂ) (hfm : Measurable[AutomorphicForm.glBorelOf A] f)
    (hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C)
    {I₁ I₂ : ℂ} (h₁ : AutomorphicForm.IsOrbitalIntegralOn A μ γ τ f I₁)
    (h₂ : AutomorphicForm.IsOrbitalIntegralOn A μ γ τ f I₂) : I₁ = I₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsOrbitalIntegralOn_unique_of_isRegularSemisimple.solution
