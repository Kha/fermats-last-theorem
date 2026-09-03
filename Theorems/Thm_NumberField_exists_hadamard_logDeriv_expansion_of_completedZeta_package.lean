import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package

theorem NumberField.exists_hadamard_logDeriv_expansion_of_completedZeta_package
    (K : Type) [Field K] [NumberField K] (Λ : ℂ → ℂ)
    (hΛdiff : DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ))
    (hΛFE : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s)
    (hΛeq : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s)
    (hB1 : ∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) ∧
        ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖)
    (hEnd : ∀ ξ : ℂ → ℂ, Differentiable ℂ ξ →
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) → ξ 0 ≠ 0 ∧ ξ 1 ≠ 0)
    (hSL : ∀ C : ℝ, ∃ s : ℂ, 2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
        C * ‖s‖ < Real.log ‖s * (s - 1) * Λ s‖) :
    ∃ (B : ℂ) (ρ : ℕ → ℂ),
      (∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1) ∧
      Summable (fun j => (Complex.normSq (ρ j))⁻¹) ∧
      ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
        logDeriv (fun z => z * (z - 1) * Λ z) s = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.solution
