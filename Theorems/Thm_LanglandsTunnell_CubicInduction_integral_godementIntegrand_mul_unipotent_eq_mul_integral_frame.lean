import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal~modulus_adicCompletion_eq_nnnorm LanglandsTunnell.CubicInduction NumberField.StandardAddChar"

theorem LanglandsTunnell.CubicInduction.integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame
    (v : HeightOneSpectrum (𝓞 ℚ)) (θ : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hθn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → θ x = 1)
    (hθn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ θ x ≠ 1)
    (lam : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (Ψ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hΨsb : ∀ k : GL (Fin 2) (v.adicCompletion ℚ), IsSchwartzBruhat (fun X => Ψ X k))
    (hΨlaw : ∀ (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) (a : v.adicCompletion ℚ)
      (k : GL (Fin 2) (v.adicCompletion ℚ)), Ψ X (unipotentGL2 a * k) = θ a * Ψ X k)
    (M : GL (Fin 3) (v.adicCompletion ℚ)) (h : GL (Fin 2) (v.adicCompletion ℚ)) :
    letI := localBorel ℚ v
    ∫ a : v.adicCompletion ℚ,
        rowFourier23 v θ⁻¹
            (fun X => Ψ (X * ((M : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))
              (h * unipotentGL2 a)⁻¹)
            (godementArg v (h * unipotentGL2 a))
          * ((lam (Matrix.GeneralLinearGroup.det (h * unipotentGL2 a)) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det (h * unipotentGL2 a) : (v.adicCompletion ℚ)ˣ) :
              v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂(selfDualHaarAt ℚ v) =
      ((lam (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
        * ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ)
        * ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)
        * ∫ t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
            Ψ (((h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
                !![1, t.1, t.2.1; 0, 1, t.2.2] *
                ((M : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) h⁻¹ *
              θ (-(t.1 + t.2.2)) ∂(jacquetHaar3 v) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame.solution
