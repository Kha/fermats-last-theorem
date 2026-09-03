import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_ModularCurve_regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply
attribute [-simp] ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ

open ModularCurve ValuationSubring AlgebraicCurve IsLocalRing

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false

theorem ModularCurve.regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN
    (M q : ℕ) [NeZero M] (hq : q.Prime) (hqM : ¬ q ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {S S' : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))}
    (hS : S = modularFunctionFieldC (ResidueField ↥A) M)
    (hS' : S' = modularFunctionFieldC (ResidueField ↥A) M)
    (R : RegularProlongation A (modularFunctionFieldBar M) S)
    (R' : RegularProlongation A (modularFunctionFieldBar M) S')
    (hj : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full M (jq_mem M))⟩ : modularFunctionFieldBar M)
        ∈ R.integers,
      (R.residue ⟨_, h⟩ : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (hjM : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full M (dvd_refl M))⟩ : modularFunctionFieldBar M)
        ∈ R.integers,
      (R.residue ⟨_, h⟩ : LaurentSeries (ResidueField ↥A)) = jqNModC (ResidueField ↥A) M)
    (hj' : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full M (jq_mem M))⟩ : modularFunctionFieldBar M)
        ∈ R'.integers,
      (R'.residue ⟨_, h⟩ : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (hjM' : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full M (dvd_refl M))⟩ : modularFunctionFieldBar M)
        ∈ R'.integers,
      (R'.residue ⟨_, h⟩ : LaurentSeries (ResidueField ↥A)) = jqNModC (ResidueField ↥A) M) :
    R.integers = R'.integers ∧
      ∀ (f : modularFunctionFieldBar M) (h : f ∈ R.integers) (h' : f ∈ R'.integers),
        (R.residue ⟨f, h⟩ : LaurentSeries (ResidueField ↥A))
          = (R'.residue ⟨f, h'⟩ : LaurentSeries (ResidueField ↥A)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN.solution
