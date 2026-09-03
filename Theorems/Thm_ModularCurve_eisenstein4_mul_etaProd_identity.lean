import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_eisenstein4_mul_etaProd_identity
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.eisenstein4_mul_etaProd_identity :
    HahnSeries.ofPowerSeries ℤ ℤ eisenstein4 * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16 *
        qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8) * qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) =
      qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 48) +
        224 * HahnSeries.single (1 : ℤ) (1 : ℤ) * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 *
          qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24) * qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) +
        256 * HahnSeries.single (2 : ℤ) (1 : ℤ) * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16 *
          qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 32) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisenstein4_mul_etaProd_identity.solution
