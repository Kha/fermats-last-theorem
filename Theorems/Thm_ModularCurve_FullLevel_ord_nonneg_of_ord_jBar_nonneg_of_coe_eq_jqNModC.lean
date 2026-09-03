import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup AlgebraicCurve

theorem ModularCurve.FullLevel.ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (J : ↥(fieldBar q M'))
    (hJ : ((J : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) q)
    (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))
    (hP : 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M'))) :
    0 ≤ P.ord (J : ↥(fieldBar q M')) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC.solution
