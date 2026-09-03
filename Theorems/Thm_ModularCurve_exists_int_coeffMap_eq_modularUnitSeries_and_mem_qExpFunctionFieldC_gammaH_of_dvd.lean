import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

set_option autoImplicit false

open ModularCurve hiding modularUnitSeries_mem_modularFunctionFieldFull isIntegral_adjoin_jq_modularUnitSeries modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
open scoped MatrixGroups

theorem ModularCurve.exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    (∃ x : LaurentSeries ℤ,
        coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p ∧
        x.coeff (1 - (p : ℤ)) = 1 ∧ ∀ n : ℤ, n < 1 - (p : ℤ) → x.coeff n = 0) ∧
      modularUnitSeries p ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) ∧
      IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularUnitSeries p) ∧
      IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularUnitSeries p)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd.solution
