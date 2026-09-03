import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_hasProd_localZeta31_dualWhittakerFn3_of_isInducedSphericalAt_of_three_le
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  NumberField.InfinitePlace LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.hasProd_localZeta31_dualWhittakerFn3_of_isInducedSphericalAt_of_three_le
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w → w ∈ S)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hsph : ∀ v, v ∉ S →
      IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (Wloc v))
    (h1 : ∀ v, v ∉ S → Wloc v 1 = 1)
    (htv : ∀ v, v ∉ S → HasSphericalTorusValuesAt (inducedCoeff K μ) v (Wloc v))
    (hlaw : ∀ v, v ∉ S → IsGL3PsiWhittakerFn (psiLoc ψ v) (Wloc v))
    (hψ0 : ∀ v, v ∉ S → ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1)
    (hψ1 : ∀ v, v ∉ S → ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hχU : ∀ v, v ∉ S → TateGlobal.IsUnramifiedCharAt χ v)
    (σ₀ : ℝ) (hσ₀ : 3 ≤ σ₀) :
    (∀ v, v ∉ S →
      letI := localBorel ℚ v
      Integrable (fun y => dualWhittakerFn3 (Wloc v) (lowerUnipotent21 y)) (selfDualHaarAt ℚ v)) ∧
    (∀ v, v ∉ S → ∀ s : ℂ, σ₀ < s.re →
      letI := localBorel ℚ v
      ((selfDualHaarAt ℚ v).real {u : v.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
        ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
          localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            (selfDualHaarAt ℚ v) (dualWhittakerFn3 (Wloc v)) (TateGlobal.localChar χ v) s 1 =
        ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval
            (((TateGlobal.localChar χ v (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹) ∧
    (Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      letI := localBorel ℚ v.1
      ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)))⁻¹
          * (∫ y, ‖dualWhittakerFn3 (Wloc v.1) (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v.1)) - 1) ∧
    (∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          letI := localBorel ℚ v.1
          ((selfDualHaarAt ℚ v.1).real {u : v.1.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
          ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)) : ℂ)⁻¹ *
            localZeta31 v.1 (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v.1)))
              (selfDualHaarAt ℚ v.1) (dualWhittakerFn3 (Wloc v.1)) (TateGlobal.localChar χ v.1) s 1)
        (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
          ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v.1).eval
              (((TateGlobal.localChar χ v.1 (NumberField.AdelicLevel.uniformizerUnit ℚ v.1) : ℂˣ) : ℂ) *
                (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)))⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_hasProd_localZeta31_dualWhittakerFn3_of_isInducedSphericalAt_of_three_le.solution
