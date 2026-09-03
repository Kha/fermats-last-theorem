import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_jqNGen ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open ModularCurve in

theorem ModularCurve.exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap
    (κ : Type*) [Field κ] [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (∃ w : ↥(modularFunctionFieldC κ N) ≃ₐ[κ] ↥(modularFunctionFieldC κ N),
        w ⟨jqModC κ, jqModC_mem κ N⟩ = ⟨jqNModC κ N, jqNModC_mem κ N⟩ ∧
          w ⟨jqNModC κ N, jqNModC_mem κ N⟩ = ⟨jqModC κ, jqModC_mem κ N⟩) ∧
    (∀ w : ↥(modularFunctionFieldC κ N) ≃ₐ[κ] ↥(modularFunctionFieldC κ N),
        w ⟨jqModC κ, jqModC_mem κ N⟩ = ⟨jqNModC κ N, jqNModC_mem κ N⟩ →
        w ⟨jqNModC κ N, jqNModC_mem κ N⟩ = ⟨jqModC κ, jqModC_mem κ N⟩ →
        ∃ w' : ↥(charLDegeneracyRoof κ N ℓ) ≃ₐ[κ] ↥(charLDegeneracyRoof κ N ℓ),
          (∀ x, w' (heckeAlphaC κ N ℓ x) = heckeBetaC κ N ℓ (w x)) ∧
            (∀ x, w' (heckeBetaC κ N ℓ x) = heckeAlphaC κ N ℓ (w x))) ∧
    (¬ ℓ ∣ N →
        ∃ w'' : ↥(charLDegeneracyRoof κ N ℓ) ≃ₐ[κ] ↥(charLDegeneracyRoof κ N ℓ),
          (∀ x, w'' (heckeAlphaC κ N ℓ x) = heckeBetaC κ N ℓ x) ∧
            (∀ x, w'' (heckeBetaC κ N ℓ x) = heckeAlphaC κ N ℓ x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap.solution
