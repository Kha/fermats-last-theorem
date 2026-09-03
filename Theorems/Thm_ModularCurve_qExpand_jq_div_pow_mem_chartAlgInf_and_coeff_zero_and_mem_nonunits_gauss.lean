import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_jq_div_pow_mem_chartAlgInf_and_coeff_zero_and_mem_nonunits_gauss
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open scoped MatrixGroups
open Polynomial ModularCurve AlgebraicCurve
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.qExpand_jq_div_pow_mem_chartAlgInf_and_coeff_zero_and_mem_nonunits_gauss
    (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ (LaurentSeries ℚ))
    (j : ↥K) (hj : (j : LaurentSeries ℚ) = jqModC ℚ) [Fact (j ≠ 0)]
    (j' : ↥K) (hj' : (j' : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ))

    (σ : ↥K ≃ₐ[ℚ] ↥K) (hσj : σ j = j') (hσj' : σ j' = j)

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)) :
    let u : ↥K := j⁻¹
    let t : ↥K := j' * u ^ p

    t ∈ TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥K j ∧

    ((t : ↥K) : LaurentSeries ℚ).coeff 0 = 1 ∧
    ((σ t : ↥K) : LaurentSeries ℚ).coeff 0 = 0 ∧

    (t - 1 ∈ W₀.nonunits ∧ ((σ (t - 1) : ↥K) : LaurentSeries ℚ).coeff 0 = -1) ∧
    (t ^ p - u ^ (p ^ 2 - 1) ∈ (W₀.comap σ.toAlgHom.toRingHom).nonunits ∧
      ((t ^ p - u ^ (p ^ 2 - 1) : ↥K) : LaurentSeries ℚ).coeff 0 = 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_jq_div_pow_mem_chartAlgInf_and_coeff_zero_and_mem_nonunits_gauss.solution
