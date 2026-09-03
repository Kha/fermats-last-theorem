import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AutomorphicForm_SmoothingKernel
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_modulus_det_mul_apply_antidiagonal_mul_transposeInvN_mem_principalSeries2
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_modulus_det_mul_apply_antidiagonal_mul_transposeInvN_mem_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    ∃ χ' : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ),
      (∀ a : (p.adicCompletion ℚ)ˣ,
        ((χ' 0 a : ℂˣ) : ℂ) = ((χ 1 a : ℂˣ) : ℂ)⁻¹ * (((modulus (a : p.adicCompletion ℚ) : ℝ)) : ℂ)) ∧
      (∀ a : (p.adicCompletion ℚ)ˣ,
        ((χ' 1 a : ℂˣ) : ℂ) = ((χ 0 a : ℂˣ) : ℂ)⁻¹ * (((modulus (a : p.adicCompletion ℚ) : ℝ)) : ℂ)) ∧
      (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        (((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) : ℂ) *
          f (w₀ * AutomorphicForm.transposeInvN (Fin 2) h)) ∈ principalSeries2 p χ' := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_modulus_det_mul_apply_antidiagonal_mul_transposeInvN_mem_principalSeries2.solution
