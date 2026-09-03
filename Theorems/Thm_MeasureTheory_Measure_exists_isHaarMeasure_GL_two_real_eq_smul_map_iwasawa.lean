import Mathlib
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_iwasawa

set_option autoImplicit false

open MeasureTheory AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates

theorem MeasureTheory.Measure.exists_isHaarMeasure_GL_two_real_eq_smul_map_iwasawa
    [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]
    [MeasurableSpace (rowIsometrySubgroup ℝ)] [BorelSpace (rowIsometrySubgroup ℝ)]
    (μ : Measure (GL (Fin 2) ℝ)) [μ.IsHaarMeasure]
    (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧
      μ = c • Measure.map
        (fun q : (ℝ × ℝ × ℝ) × rowIsometrySubgroup ℝ =>
          (if h : 0 < q.1.2.1 ∧ 0 < q.1.2.2 then
              upperUnit (q.1.2.2 * q.1.2.1) (q.1.2.2 * q.1.1) q.1.2.2
                (mul_pos h.2 h.1).ne' h.2.ne'
            else 1) * (q.2 : GL (Fin 2) ℝ))
        (((volume.restrict (Set.univ ×ˢ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))).withDensity
            (fun q => ENNReal.ofReal ((q.2.1 ^ 2)⁻¹ * q.2.2⁻¹))).prod ν) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_iwasawa.solution
