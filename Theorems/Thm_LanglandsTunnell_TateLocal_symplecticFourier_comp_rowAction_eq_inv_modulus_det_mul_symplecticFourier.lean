import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory open LanglandsTunnell.TateLocal hiding modulus_adicCompletion_eq_nnnorm

theorem LanglandsTunnell.TateLocal.symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Φ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) (w : Fin 2 → p.adicCompletion ℚ) :
    letI := localBorel ℚ p
    ∫ u : Fin 2 → p.adicCompletion ℚ, Φ (fun j : Fin 2 => u 0 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + u 1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
        NumberField.StandardAddChar.psiLocal ℚ p (u 1 * w 0 - u 0 * w 1) ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) =
      (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹ *
        ∫ u : Fin 2 → p.adicCompletion ℚ, Φ u *
          NumberField.StandardAddChar.psiLocal ℚ p
            (u 1 * (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)⁻¹ * (w 0 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 + w 1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0)) -
             u 0 * (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)⁻¹ * (w 0 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1 + w 1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)))
          ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier.solution
