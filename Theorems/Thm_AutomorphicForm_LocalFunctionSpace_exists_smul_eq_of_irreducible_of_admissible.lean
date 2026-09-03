import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_LocalFunctionSpace_exists_smul_eq_of_irreducible_of_admissible

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.exists_smul_eq_of_irreducible_of_admissible
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (S : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ S)
    (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
    (hirr : ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = S)
    (hadm : ∀ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
        (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T)
    (Φ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hΦS : ∀ W ∈ S, Φ W ∈ S)
    (hΦρ : ∀ W ∈ S, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), Φ (fun g => W (g * k)) = fun g => Φ W (g * k)) :
    ∃ c : ℂ, ∀ W ∈ S, Φ W = c • W := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalFunctionSpace_exists_smul_eq_of_irreducible_of_admissible.solution
