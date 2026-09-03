import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Constructions
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv
set_option autoImplicit false
open MeasureTheory

theorem MeasureTheory.Measure.exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv
    [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]
    (μ : Measure (GL (Fin 2) ℝ)) [μ.IsHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧
      μ = c • Measure.map
        (fun A : Fin 2 → Fin 2 → ℝ =>
          if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℝ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal (((Matrix.of A).det ^ 2)⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.solution
