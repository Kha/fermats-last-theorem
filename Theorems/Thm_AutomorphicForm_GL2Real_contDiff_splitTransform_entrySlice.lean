import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.contDiff_splitTransform_entrySlice
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ × P => splitTransform (entrySlice Φ q.2.2) q.1 q.2.1) ∧
      HasCompactSupport (fun q : ℝ × ℝ × P => splitTransform (entrySlice Φ q.2.2) q.1 q.2.1) ∧
      tsupport (fun q : ℝ × ℝ × P => splitTransform (entrySlice Φ q.2.2) q.1 q.2.1) ⊆
        {q | q.1 * q.2.1 ≠ 0} ∧
      ∀ (a₁ a₂ : ℝ) (p : P),
        splitTransform (entrySlice Φ p) a₂ a₁ = splitTransform (entrySlice Φ p) a₁ a₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.solution
