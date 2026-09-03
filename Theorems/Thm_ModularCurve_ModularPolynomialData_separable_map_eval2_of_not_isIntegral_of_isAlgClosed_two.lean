import Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed_two
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4
attribute [-simp] ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero
attribute [-simp] ModularForm.val_upperTriangularGL WeierstrassCurve.veluX_empty

open Polynomial ModularCurve
theorem ModularCurve.ModularPolynomialData.separable_map_eval2_of_not_isIntegral_of_isAlgClosed_two
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (data : ModularPolynomialData 2) (jv : F) (hjv : ¬ _root_.IsIntegral ℤ jv) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) jv)).Separable := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed_two.solution
