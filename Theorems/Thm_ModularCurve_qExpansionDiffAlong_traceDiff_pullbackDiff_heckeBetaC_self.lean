import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self
attribute [-instance] ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
attribute [-simp] AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ

open ModularCurve AlgebraicCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (τ : modularFunctionFieldC K p ≃ₐ[K] modularFunctionFieldC K p)
    (hτ₁ : τ ⟨jqModC K, jqModC_mem K p⟩ = ⟨jqNModC K p, jqNModC_mem K p⟩)
    (hτ₂ : τ ⟨jqNModC K p, jqNModC_mem K p⟩ = ⟨jqModC K, jqModC_mem K p⟩)
    (ω : Ω[modularFunctionFieldC K p⁄K]) :
    (letI := AlgebraicCurve.algebraAlong (heckeAlphaC K p p)
     haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K p p)
     qExpansionDiffAlong (modularFunctionFieldC K p).val
      (traceDiff K (modularFunctionFieldC K p) (charLDegeneracyRoof K p p)
        (pullbackDiff (heckeBetaC K p p) ω)))
    = (p : K) • qExpand K p (qExpansionDiffAlong (modularFunctionFieldC K p).val ω)
      + ∑ b ∈ Finset.Ico 1 p, qTwist (ζ ^ b)
          (qExpansionDiffAlong ((modularFunctionFieldC K p).val.comp
            (τ : modularFunctionFieldC K p →ₐ[K] modularFunctionFieldC K p)) ω) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.solution
