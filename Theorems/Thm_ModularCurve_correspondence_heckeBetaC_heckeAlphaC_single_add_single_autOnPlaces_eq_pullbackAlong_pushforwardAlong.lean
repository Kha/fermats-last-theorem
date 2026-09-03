import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
attribute [-simp] AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply
set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong
    (M s : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] (p : ℕ) [CharP k p] (hp : ¬ p ∣ M * s)
    (hM : jqNModC k M ∈ modularFunctionFieldC k (M * s)) (hS : jqNModC k s ∈ modularFunctionFieldC k (M * s))
    (σ : ↥(modularFunctionFieldC k (M * s)) ≃ₐ[k] ↥(modularFunctionFieldC k (M * s)))
    (hσ : IsAtkinLehnerLevelAut k M s hM hS σ) :
    ∀ [HasPrincipalDivisors k ↥(charLDegeneracyRoof k (M * s) s)]
      [HasPrincipalDivisors k ↥(modularFunctionFieldC k (M * s))]
      (hα : HeckeAlphaCIntegral k (M * s) s) (hβ : HeckeBetaCIntegral k (M * s) s)
      (ha : (levelAlphaC k M s hM).toRingHom.IsIntegral) (hb : (levelBetaC k M s hS).toRingHom.IsIntegral)
      (x : Place k ↥(modularFunctionFieldC k (M * s))),
      Divisor.correspondence (heckeBetaC k (M * s) s) (heckeAlphaC k (M * s) s) hβ hα (Finsupp.single x 1)
          + Finsupp.single (autOnPlaces k M s σ x) 1
        = Divisor.pullbackAlong (levelBetaC k M s hS) hb
            (Divisor.pushforwardAlong (levelAlphaC k M s hM) ha (Finsupp.single x 1)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong.solution
