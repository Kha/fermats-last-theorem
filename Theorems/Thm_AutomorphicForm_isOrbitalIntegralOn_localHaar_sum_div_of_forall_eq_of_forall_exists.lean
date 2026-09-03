import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

theorem
AutomorphicForm.isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ∀ u₁ ∈ AutomorphicForm.localIntegralSet K v, ∀ u₂ ∈ AutomorphicForm.localIntegralSet K v,
        f (u₁ * g * u₂) = f g)
    (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∀ u ∈ AutomorphicForm.localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov :
      ∀ x : GL (Fin 2) (v.adicCompletion K), f (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S,
          ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
            ∃ u ∈ AutomorphicForm.localIntegralSet K v, x = t * s * u) :
    AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ f
      (∑ s ∈ S, f (s⁻¹ * γ * s) /
        ((τ {t | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈
            AutomorphicForm.localIntegralSet K v}).toReal : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists.solution
