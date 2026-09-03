import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair
attribute [-instance] AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

namespace ModularCurve.DRModelPackageLevel

theorem exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (W : Fin 2 → ValuationSubring ↥(modularFunctionFieldFull (N₀ * q)))

    (hW₀ : ∀ f : ↥(modularFunctionFieldFull (N₀ * q)), f ∈ W 0 ↔
      ∃ x y : LaurentSeries ℤ, ModularCurve.coeffMap (Int.castRingHom (ZMod q)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * ModularCurve.coeffMap (Int.castRingHom ℚ) y = ModularCurve.coeffMap (Int.castRingHom ℚ) x)

    (hW₁ : ∀ f : ↥(modularFunctionFieldFull (N₀ * q)), f ∈ W 1 ↔ ModularCurve.atkinLehnerInvolutionFull N₀ q f ∈ W 0)
    (hne : W 0 ≠ W 1)

    (habove : ∀ i, ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W i).nonunits ∧
      (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod q)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)))
            ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N₀ * q) (ModularCurve.jq_mem (N₀ * q))⟩ P ∈ W i ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)))
            ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N₀ * q) (ModularCurve.jq_mem (N₀ * q))⟩ P)⁻¹ ∈ W i) ∧
      (∀ f ∈ (W i).nonunits, f * ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹ ∈ W i))

    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull (N₀ * q)),
      ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ∈ V.nonunits →
      (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod q)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)))
            ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N₀ * q) (ModularCurve.jq_mem (N₀ * q))⟩ P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)))
            ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N₀ * q) (ModularCurve.jq_mem (N₀ * q))⟩ P)⁻¹ ∈ V) →
      V = W 0 ∨ V = W 1) :
    ∃ P : Fin 2 → Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      (∀ (i : Fin 2) (a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)), a ∈ P i ↔ ((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W i).nonunits)) ∧
      (∀ i, (P i).IsPrime) ∧ P 0 ≠ P 1 ∧
      (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}).minimalPrimes = {P 0, P 1} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair.solution

end ModularCurve.DRModelPackageLevel
