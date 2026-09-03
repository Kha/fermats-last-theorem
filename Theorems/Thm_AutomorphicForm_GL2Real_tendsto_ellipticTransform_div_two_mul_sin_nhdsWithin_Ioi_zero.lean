import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero
    (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun q : ℝ × ℝ =>
        ((if h : Matrix.det !![r * (1 - q.2), r * (q.2 ^ 2 / q.1); -(r * q.1), r * (1 + q.2)] ≠ 0 then
            f (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) +
          (if h : Matrix.det !![r * (1 + q.2), -(r * (q.2 ^ 2 / q.1)); r * q.1, r * (1 - q.2)] ≠ 0 then
            f (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0)) / (q.1 : ℂ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) ∧
    Filter.Tendsto (fun θ : ℝ => ellipticTransform f r θ / (2 * Real.sin θ : ℂ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.univ,
        ((if h : Matrix.det !![r * (1 - q.2), r * (q.2 ^ 2 / q.1); -(r * q.1), r * (1 + q.2)] ≠ 0 then
            f (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) +
          (if h : Matrix.det !![r * (1 + q.2), -(r * (q.2 ^ 2 / q.1)); r * q.1, r * (1 - q.2)] ≠ 0 then
            f (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0)) / (q.1 : ℂ))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero.solution
