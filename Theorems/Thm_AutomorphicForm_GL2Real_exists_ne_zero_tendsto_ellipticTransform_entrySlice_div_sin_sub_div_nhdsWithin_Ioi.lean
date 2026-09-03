import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi :
    ∃ C : ℝ, C ≠ 0 ∧
      ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
        tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} →
        ∀ (p : P) (r : ℝ), 0 < r →
          ∃ L : ℂ,
            Filter.Tendsto (fun θ : ℝ => ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ∧
            Filter.Tendsto
              (fun θ : ℝ => (ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ) - L) / (θ : ℂ))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds ((C : ℂ) * Φ (Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ)), p))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi.solution
