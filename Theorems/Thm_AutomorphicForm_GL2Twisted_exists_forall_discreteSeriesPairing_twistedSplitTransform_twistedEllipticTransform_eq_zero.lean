import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted

theorem
AutomorphicForm.GL2Twisted.exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
    (hΦr : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (Matrix.of q.1 * ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), q.2))))
    (hΦl : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of q.1), q.2)))) :
    ∃ N : ℕ, ∀ p : P, ∀ k > N, ∀ r > 0,
      discreteSeriesPairing k
        (fun a₁ a₂ =>
          twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) a₁ a₂)
        (fun r' θ =>
          twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r' θ)
        r = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.solution
