import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_mem_x1x0FunctionFieldC_mul_of_mem
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

p2m_open "ModularCurve~qExpand_image_intFormRatiosC_subset"

theorem ModularCurve.qExpand_mem_x1x0FunctionFieldC_mul_of_mem
    (N t p : ℕ) [NeZero N] [NeZero t] [Fact p.Prime]
    {y : LaurentSeries ℚ} (hy : y ∈ x1x0FunctionFieldC ℚ N (N * t)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    qExpand ℚ p y ∈ x1x0FunctionFieldC ℚ N (N * t * p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_mem_x1x0FunctionFieldC_mul_of_mem.solution
