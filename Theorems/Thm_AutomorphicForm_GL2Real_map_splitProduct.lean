import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_map_splitProduct
set_option autoImplicit false
open MeasureTheory

theorem AutomorphicForm.GL2Real.map_splitProduct :
    Measure.map
      (fun p : Fin 2 → Fin 2 → ℝ => Matrix.of.symm
      (((if h : p 0 0 * p 0 1 ≠ 0 then
            upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) h * (rotation (p 1 0))⁻¹
          else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)))
      ((volume.restrict
        {p : Fin 2 → Fin 2 → ℝ | p 0 0 * p 0 1 ≠ 0 ∧ 0 < p 1 0 ∧ p 1 0 < Real.pi}).withDensity
        (fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal |p 0 0 * p 0 1|)) =
      volume.restrict
        {m : Fin 2 → Fin 2 → ℝ | m 0 0 * m 1 1 - m 0 1 * m 1 0 ≠ 0 ∧ m 1 0 ≠ 0} := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_map_splitProduct.solution
