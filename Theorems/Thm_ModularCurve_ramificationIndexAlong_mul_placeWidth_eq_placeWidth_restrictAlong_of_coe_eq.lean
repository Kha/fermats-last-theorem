import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (M M' : ℕ) [NeZero M] [NeZero M']
    (φ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k M')) (hφ : φ.toRingHom.IsIntegral)
    (hcoe : ∀ x, ((φ x : ↥(modularFunctionFieldC k M')) : LaurentSeries k) = x)
    (p : Place k ↥(modularFunctionFieldC k M'))
    (hdiv : placeRamificationJ M' p ∣ jWidth (p.evalAt (jGeomGen k M'))) :
    Place.ramificationIndexAlong φ p * placeWidth M' p = placeWidth M (Place.restrictAlong φ hφ p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq.solution
