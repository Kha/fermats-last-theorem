import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Twisted_twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Twisted

theorem AutomorphicForm.GL2Twisted.twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin
    (P : Type) [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ContinuousOn (fun q : ℝ × ℝ × P =>
        twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1)
        {q | 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi} ∧
      (∀ C : Set ℝ, IsCompact C → C ⊆ Set.Ioi 0 →
        ∃ K : ℝ, ∀ r ∈ C, ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ p : P,
          ‖twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r θ‖ ≤
            K * |Real.sin θ|) ∧
      ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
        ∀ (r θ : ℝ) (p : P), (r, p) ∉ K →
          twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r θ = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Twisted_twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin.solution
