import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_forall_mem_chartAlgInf_jFull_exists_mul_mem_and_symm_of_coe_eq_qExpand
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel ModularCurve

theorem ModularCurve.forall_mem_chartAlgInf_jFull_exists_mul_mem_and_symm_of_coe_eq_qExpand
    (N p : ℕ) [NeZero N] [Fact p.Prime] [NeZero p]
    (jp : ↥(modularFunctionFieldFull N)) (hjp : ((jp : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    [Fact (jp ≠ 0)] :
    (∀ y ∈ chartAlgInf ℤ ↥(modularFunctionFieldFull N) jp,
        ∃ s ∈ chartAlgInf ℤ ↥(modularFunctionFieldFull N) (IgusaScheme.jFull N),
          (∃ a ∈ chartAlgInf ℤ ↥(modularFunctionFieldFull N) (IgusaScheme.jFull N), s = 1 + (IgusaScheme.jFull N)⁻¹ * a) ∧
            s * y ∈ chartAlgInf ℤ ↥(modularFunctionFieldFull N) (IgusaScheme.jFull N)) ∧
    (∀ y ∈ chartAlgInf ℤ ↥(modularFunctionFieldFull N) (IgusaScheme.jFull N),
        ∃ s ∈ chartAlgInf ℤ ↥(modularFunctionFieldFull N) jp,
          (∃ a ∈ chartAlgInf ℤ ↥(modularFunctionFieldFull N) jp, s = 1 + jp⁻¹ * a) ∧
            s * y ∈ chartAlgInf ℤ ↥(modularFunctionFieldFull N) jp) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_forall_mem_chartAlgInf_jFull_exists_mul_mem_and_symm_of_coe_eq_qExpand.solution
