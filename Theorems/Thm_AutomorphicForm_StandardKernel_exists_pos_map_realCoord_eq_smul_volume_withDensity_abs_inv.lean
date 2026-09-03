import Definitions.Def_AutomorphicForm_SmoothingKernel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_StandardKernel_exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.StandardKernel.exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure] :
    ∃ κ : ℝ, 0 < κ ∧
      MeasureTheory.Measure.map
          (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
        ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
          fun y => ENNReal.ofReal |y|⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_StandardKernel_exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv.solution
