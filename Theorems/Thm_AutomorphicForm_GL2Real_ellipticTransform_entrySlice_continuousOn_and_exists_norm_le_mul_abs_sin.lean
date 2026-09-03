import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_ellipticTransform_entrySlice_continuousOn_and_exists_norm_le_mul_abs_sin

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.ellipticTransform_entrySlice_continuousOn_and_exists_norm_le_mul_abs_sin
    (P : Type) [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ContinuousOn (fun q : ℝ × ℝ × P => ellipticTransform (entrySlice Φ q.2.2) q.1 q.2.1)
        {q | 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi} ∧
      ∀ C : Set ℝ, IsCompact C → C ⊆ Set.Ioi 0 →
        ∃ K : ℝ, ∀ r ∈ C, ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ p : P,
          ‖ellipticTransform (entrySlice Φ p) r θ‖ ≤ K * |Real.sin θ| := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_ellipticTransform_entrySlice_continuousOn_and_exists_norm_le_mul_abs_sin.solution
