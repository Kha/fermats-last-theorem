import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
import P2M.Sol.S_ModularCurve_deg_ne_zero_modularFunctionFieldC
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import P2M.Sol.S_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
import P2M.Util
namespace P2MW.S_ModularCurve_place_deg_eq_one_charLDegeneracyRoof
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
open ModularCurve AlgebraicCurve
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] (N q : ℕ) [NeZero N] [NeZero q]
    (W : AlgebraicCurve.Place k (charLDegeneracyRoof k N q)) :
    W.deg = 1 := by

  refine AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed W ?_

  letI := algebraAlong (heckeAlphaC k N q)
  haveI := isScalarTower_along (heckeAlphaC k N q)
  haveI hFin : Module.Finite (modularFunctionFieldC k N) (charLDegeneracyRoof k N q) :=
    ModularCurve.finiteAlong_heckeAlphaC k N q
  haveI : Algebra.IsIntegral (modularFunctionFieldC k N) (charLDegeneracyRoof k N q) :=
    Algebra.IsIntegral.of_finite _ _

  have htower : (W.restrict (modularFunctionFieldC k N)).deg
      * W.inertiaDeg (modularFunctionFieldC k N) = W.deg :=
    W.deg_restrict_mul_inertiaDeg
  rw [← htower]

  refine Nat.mul_ne_zero ?_ ?_
  · exact ModularCurve.deg_ne_zero_modularFunctionFieldC k N
      (W.restrict (modularFunctionFieldC k N))
  · exact Nat.ne_of_gt
      (AlgebraicCurve.Place.inertiaDeg_pos_of_finiteDimensional W)
