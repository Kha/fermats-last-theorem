import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
  AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (θ : AddChar (p.adicCompletion ℚ) ℂ)
    (hθk : ∃ k : ℤ, ∀ y : p.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → θ y = 1)
    (hθ1 : θ ≠ 1)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      ∃ (M₀ : ℤ) (S : Finset ℤ) (c : ℤ → ℂ), ∀ (u : ℂ) (M : ℤ), M₀ ≤ M →
        IntegrableOn (fun y : p.adicCompletion ℚ =>
            f (w₀ * unipotentGL2 y * g) *
              ((‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                    Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
                  max ‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
                    ‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 : ℝ) : ℂ) ^ u * θ y)
          {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M} ν ∧
        ∫ y in {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M},
            f (w₀ * unipotentGL2 y * g) *
              ((‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                    Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
                  max ‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
                    ‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 : ℝ) : ℂ) ^ u * θ y ∂ν =
          ∑ j ∈ S, c j * (Ideal.absNorm p.asIdeal : ℂ) ^ ((j : ℂ) * u) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow.solution
