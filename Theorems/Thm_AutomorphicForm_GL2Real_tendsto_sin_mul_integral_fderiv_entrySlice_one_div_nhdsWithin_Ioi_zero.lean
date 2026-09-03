import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (p : P) (r : ℝ) (hr : 0 < r) :
    Filter.Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.univ,
        (fderiv ℝ (fun M => Φ (M, p))
            (Matrix.of.symm !![r * (Real.cos θ - q.2), r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1);
              -(r * q.1), r * (Real.cos θ + q.2)])
            (Matrix.of.symm !![1, 0; 0, 1]) +
          fderiv ℝ (fun M => Φ (M, p))
            (Matrix.of.symm !![r * (Real.cos θ + q.2), -(r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1));
              r * q.1, r * (Real.cos θ - q.2)])
            (Matrix.of.symm !![1, 0; 0, 1])) / (q.1 : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.solution
