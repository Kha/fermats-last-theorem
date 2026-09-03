import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_linearMap_stabilised_jacquetIntegral_principalSeries2
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
  AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_linearMap_stabilised_jacquetIntegral_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (θ : AddChar (p.adicCompletion ℚ) ℂ)
    (hθk : ∃ k : ℤ, ∀ y : p.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → θ y = 1)
    (hθ1 : θ ≠ 1) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      ∃ Λ : ↥(principalSeries2 p χ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),

        (∀ (f : ↥(principalSeries2 p χ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), ∃ M₀ : ℤ, ∀ M : ℤ, M₀ ≤ M →
            IntegrableOn (fun y : p.adicCompletion ℚ =>
                (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (w₀ * unipotentGL2 y * g) * θ y)
              {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M} ν ∧
            Λ f g = ∫ y in {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M},
              (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (w₀ * unipotentGL2 y * g) * θ y ∂ν) ∧

        (∀ (f : ↥(principalSeries2 p χ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
            Integrable (fun y : p.adicCompletion ℚ =>
                (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (w₀ * unipotentGL2 y * g) * θ y) ν →
            Λ f g = ∫ y, (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (w₀ * unipotentGL2 y * g) * θ y ∂ν) ∧

        (∀ (f : ↥(principalSeries2 p χ)) (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
            Λ f (unipotentGL2 x * g) = (θ x)⁻¹ * Λ f g) ∧

        (∀ (f : ↥(principalSeries2 p χ)) (h g : GL (Fin 2) (p.adicCompletion ℚ)),
            Λ (principalSeries2Rep χ h f) g = Λ f (g * h)) ∧

        (∃ f : ↥(principalSeries2 p χ), Λ f 1 ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_stabilised_jacquetIntegral_principalSeries2.solution
