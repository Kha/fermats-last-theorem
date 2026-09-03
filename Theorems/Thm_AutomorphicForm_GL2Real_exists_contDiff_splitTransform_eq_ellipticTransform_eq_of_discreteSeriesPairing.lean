import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing

set_option autoImplicit false

open MeasureTheory Polynomial AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (H : ℝ × ℝ × P → ℂ) (E : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H)
    (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p))
    (hEc : ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
      ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0)
    (hEi : ∀ (r : ℝ) (p : P), IntervalIntegrable (fun θ => E (r, θ, p)) volume 0 Real.pi)
    (hEcont : ContinuousOn E {q | 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi})
    (hEmode : ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) fun q : ℝ × P =>
      ∫ θ in (0 : ℝ)..Real.pi, E (q.1, θ, q.2) * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ))
    (hvanish : ∃ N : ℕ, ∀ p : P, ∀ k > N, ∀ r > 0,
      discreteSeriesPairing k (fun a₁ a₂ => H (a₁, a₂, p)) (fun r' θ => E (r', θ, p)) r = 0) :
    ∃ F : (Fin 2 → Fin 2 → ℝ) × P → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ {r | IsUnit (Matrix.det (Matrix.of r.1))} ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
        fun r : (Fin 2 → Fin 2 → ℝ) × P =>
          F (Matrix.of.symm (Matrix.of r.1 * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), r.2))) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
        fun r : (Fin 2 → Fin 2 → ℝ) × P =>
          F (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of r.1), r.2))) ∧
      (∀ (n : ℕ) (c : Fin n → ℂ) (q : Fin n → P),
        (∀ a : ℝ × ℝ, ∑ j, c j * H (a.1, a.2, q j) = 0) →
          (∀ b : ℝ × ℝ, 0 < b.1 → 0 < b.2 → b.2 < Real.pi → ∑ j, c j * E (b.1, b.2, q j) = 0) →
            ∀ M : Fin 2 → Fin 2 → ℝ, ∑ j, c j * F (M, q j) = 0) ∧
      (∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 → splitTransform (entrySlice F p) a₁ a₂ = H (a₁, a₂, p)) ∧
      (∀ (p : P) (r θ : ℝ), 0 < r → 0 < θ → θ < Real.pi →
        ellipticTransform (entrySlice F p) r θ = E (r, θ, p)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing.solution
