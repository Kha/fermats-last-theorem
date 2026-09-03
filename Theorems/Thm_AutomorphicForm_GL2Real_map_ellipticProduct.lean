import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_map_ellipticProduct
set_option autoImplicit false
open MeasureTheory

theorem AutomorphicForm.GL2Real.map_ellipticProduct :
    Measure.map
      (fun p : Fin 2 → Fin 2 → ℝ => Matrix.of.symm
      (((if h : 0 < p 0 0 ∧ 0 < p 1 0 then
            ellipticElt (p 0 0) (p 0 1) h.1 * (upperHalfPlaneElt (p 1 1) (p 1 0) h.2)⁻¹
          else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)))
      ((volume.restrict
        {p : Fin 2 → Fin 2 → ℝ | 0 < p 0 0 ∧ 0 < p 1 0 ∧ 0 < p 0 1 ∧ p 0 1 < 2 * Real.pi}).withDensity
        (fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal (p 0 0 ^ 3 / p 1 0 ^ 4))) =
      volume.restrict
        {m : Fin 2 → Fin 2 → ℝ | 0 < m 0 0 * m 1 1 - m 0 1 * m 1 0} := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_map_ellipticProduct.solution
