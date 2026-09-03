import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
import P2M.Util
namespace P2MW.S_ModularCurve_jqNModC_mem_chartAlgFin_of_mem
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve

theorem solution
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (N : ℕ) [NeZero N] (hN : 1 < N) (hK : ModularCurve.jqNModC L N ∈ K) :
    (⟨ModularCurve.jqNModC L N, hK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := by
  have hcoe : ModularCurve.jqNModC L N = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ N ModularCurve.jq) := by
    rw [ModularCurve.coeffEmb, coeffSemilinearAut.coeffMap_qExpand, ← jqModC_rat, coeffSemilinearAut.coeffMap_jqModC, jqNModC]
  haveI : Fact ((⟨ModularCurve.jqNModC L N, hK⟩ : ↥K) ≠ 0) :=
    ⟨fun h => jqNModC_ne_zero L N (congrArg Subtype.val h)⟩
  exact (ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
    N hN L K A j hj ⟨ModularCurve.jqNModC L N, hK⟩ hcoe).1
