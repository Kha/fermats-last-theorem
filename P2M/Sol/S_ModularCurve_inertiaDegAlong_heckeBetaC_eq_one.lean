import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_ModularCurve_place_deg_eq_one_charLDegeneracyRoof
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import P2M.Util
namespace P2MW.S_ModularCurve_inertiaDegAlong_heckeBetaC_eq_one
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem solution (M s : ℕ) [NeZero M] [NeZero s]
    {k : Type*} [Field k] [IsAlgClosed k] (hβ : HeckeBetaCIntegral k M s)
    (W : Place k ↥(charLDegeneracyRoof k M s)) :
    W.inertiaDegAlong (heckeBetaC k M s) hβ = 1 := by
  unfold AlgebraicCurve.Place.inertiaDegAlong
  letI := AlgebraicCurve.algebraAlong (heckeBetaC k M s)
  haveI := AlgebraicCurve.isScalarTower_along (heckeBetaC k M s)
  haveI := AlgebraicCurve.isIntegral_along (heckeBetaC k M s) hβ
  exact AlgebraicCurve.Place.inertiaDeg_eq_one_of_isRational W
    ((AlgebraicCurve.Place.isRational_iff_deg_eq_one W).mpr
      (ModularCurve.place_deg_eq_one_charLDegeneracyRoof k M s W))
    ((AlgebraicCurve.Place.isRational_iff_deg_eq_one _).mpr
      (ModularCurve.place_deg_eq_one_of_isAlgClosed k M _))
