import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (n : ℤ)
    (hψn : ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (V : LocalGL3 p → ℂ) (hV : IsGL3PsiWhittakerFn ψ⁻¹ V)
    (hVsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, V (g * k) = V g)
    (χ η : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hη : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((η a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ)⁻¹ * (((modulus (a : p.adicCompletion ℚ) : ℝ)) : ℂ))
    (C : ℂ) (k : ℤ) (h : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localBorel ℚ p
    ∀ (τ : Measure (p.adicCompletion ℚ)ˣ) [τ.IsHaarMeasure]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],

      (∀ h' : GL (Fin 2) (p.adicCompletion ℚ), ∃ T : Finset ℤ, ∀ j : ℤ, j ∉ T →
        ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
          dualWhittakerFn3 V (iotaGL (diagUnitGL2
            (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ j * u) * h')) *
            ((χ u : ℂˣ) : ℂ)⁻¹ ∂τ = 0) →

      (∀ V' ∈ gl3CyclicSubspace V, ∃ (Q₁ Q₂ : Polynomial ℂ) (n₀ : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p τ V' χ (weylPrime3 * transposeInv3 (iotaGL h)) σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p τ V' χ s (weylPrime3 * transposeInv3 (iotaGL h)) *
                Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n₀ : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p τ ν (dualWhittakerFn3 V') χ⁻¹
            (weylPrime3 * transposeInv3 (weylPrime3 * transposeInv3 (iotaGL h))) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p τ ν V' χ (1 - s) (weylPrime3 * transposeInv3 (iotaGL h)) *
                Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n₀ : ℂ) * s) *
                (C * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)))) →
      ∃ (P : Polynomial ℂ) (m : ℤ) (σ₀ σ₁ : ℝ) (R : Finset ℝ),
        IsLocalZeta31ConvergentAbove p τ ν (dualWhittakerFn3 V) η (iotaGL h) σ₀ ∧
        (∀ S : ℂ, σ₀ < S.re →
          localZeta31 p τ ν (dualWhittakerFn3 V) η S (iotaGL h) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * S) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-S))) ∧
        IsLocalZeta30ConvergentAbove p τ V χ (weylPrime3 * transposeInv3 (iotaGL h)) σ₁ ∧
        (∀ S : ℂ, σ₁ < (-S).re → (Ideal.absNorm p.asIdeal : ℝ) ^ S.re ∉ R →
          C * localZeta30 p τ V χ (-S) (weylPrime3 * transposeInv3 (iotaGL h)) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * S) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * S) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-S)))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_localZeta31_dualWhittakerFn3_iotaGL_eq_and_mul_localZeta30_eq_of_forall_mem_gl3CyclicSubspace_fe_of_torusShell.solution
