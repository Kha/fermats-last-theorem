import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_discreteSeriesPairing_entrySlice_eq_zero_of_weight

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.discreteSeriesPairing_entrySlice_eq_zero_of_weight
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (m : ℕ)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
    (htype : ∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      entrySlice Φ p ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * entrySlice Φ p g) :
    ∀ p : P,
      (∀ j : ℕ, m + 2 ≤ j → ∀ r : ℝ, 0 < r →
        discreteSeriesPairing j (splitTransform (entrySlice Φ p)) (ellipticTransform (entrySlice Φ p)) r = 0) ∧
      (∀ j : ℕ, 2 ≤ j → ¬ 2 ∣ j + m → ∀ r : ℝ, 0 < r →
        discreteSeriesPairing j (splitTransform (entrySlice Φ p)) (ellipticTransform (entrySlice Φ p)) r = 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_discreteSeriesPairing_entrySlice_eq_zero_of_weight.solution
