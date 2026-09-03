import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.IsWeightedOrbitalIntegralOn.unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (μ : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μ)
    (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel A γ) τ)
    (wt : GL (Fin 2) A → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), ∀ x : GL (Fin 2) A,
      wt ((t : GL (Fin 2) A) * x) = wt x)
    (f : GL (Fin 2) A → ℂ) (hfm : Measurable[AutomorphicForm.glBorelOf A] f)
    (hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C)
    {J₁ J₂ : ℂ} (h₁ : AutomorphicForm.IsWeightedOrbitalIntegralOn A μ wt γ τ f J₁)
    (h₂ : AutomorphicForm.IsWeightedOrbitalIntegralOn A μ wt γ τ f J₂) : J₁ = J₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq.solution
