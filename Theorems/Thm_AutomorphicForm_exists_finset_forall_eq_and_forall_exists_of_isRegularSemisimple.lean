import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

theorem
AutomorphicForm.exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfs : ∃ F₀ : Finset (GL (Fin 2) (v.adicCompletion K)),
      ∀ g : GL (Fin 2) (v.adicCompletion K), f g ≠ 0 → ∃ c ∈ F₀, c⁻¹ * g ∈ AutomorphicForm.localIntegralSet K v) :
    ∃ S : Finset (GL (Fin 2) (v.adicCompletion K)),
     (
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∀ u ∈ AutomorphicForm.localIntegralSet K v, s' = t * s * u → s' = s
     ) ∧
     (
      ∀ x : GL (Fin 2) (v.adicCompletion K), f (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S,
          ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
            ∃ u ∈ AutomorphicForm.localIntegralSet K v, x = t * s * u
     ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple.solution
