import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_NumberField_AdelicHaar_exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem NumberField.AdelicHaar.exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log
    (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (K : Type) [Field K] [NumberField K]
    (μ : Measure (Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K))) [μ.IsHaarMeasure]
    (a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ < b₀)
    (Φ₀ : Set (Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K)))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a₀ b₀})
    (hΦ₀ : IsFundamentalDomain
      (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) :
        Matrix.GeneralLinearGroup n K →* Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K)).range Φ₀
      (μ.restrict {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc a₀ b₀}))
    (hfin : μ Φ₀ ≠ ⊤) :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      (∀ Φ : Set (Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K)),
        IsFundamentalDomain
          (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) :
            Matrix.GeneralLinearGroup n K →* Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K)).range Φ μ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          μ (Φ ∩ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈
            Set.Icc a b}) = C * ENNReal.ofReal (Real.log (b / a))) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b → ∀ Φ : Set (Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K)),
        Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
        IsFundamentalDomain
          (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) :
            Matrix.GeneralLinearGroup n K →* Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K)).range Φ
          (μ.restrict {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈
            Set.Icc a b}) →
        μ Φ = C * ENNReal.ofReal (Real.log (b / a))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicHaar_exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log.solution
