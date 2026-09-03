import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Mathlib.Analysis.Calculus.ContDiff.Defs
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Twisted_contDiff_twistedSplitTransform

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Twisted

theorem AutomorphicForm.GL2Twisted.contDiff_twistedSplitTransform
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ × P =>
        twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1) ∧
      HasCompactSupport (fun q : ℝ × ℝ × P =>
        twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1) ∧
      tsupport (fun q : ℝ × ℝ × P =>
        twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1) ⊆
        {q | q.1 * q.2.1 ≠ 0} ∧
      ∀ (a₁ a₂ : ℝ) (p : P),
        twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) a₂ a₁ =
          twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) a₁ a₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Twisted_contDiff_twistedSplitTransform.solution
