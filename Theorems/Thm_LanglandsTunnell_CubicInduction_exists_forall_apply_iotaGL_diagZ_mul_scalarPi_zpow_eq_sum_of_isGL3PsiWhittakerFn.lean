import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField UnramifiedWhittaker

theorem
LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn
    (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (η : AddChar (v.adicCompletion ℚ) ℂ)
    (hη : ¬ ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) → η x = 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn η W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (L : ℕ) :
    ∃ (d₁ : ℕ) (c₁ : Fin d₁ → ℂ) (d₂ : ℕ) (c₂ : Fin d₂ → ℂ),
      ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
          (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(L : ℤ))) →
          ∀ g : LocalGL3 v, F (g * k) = F g) →
        (∀ k m : ℤ, k < -(L : ℤ) ∨ m < -(L : ℤ) →
          F (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k *
            scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) = 0) ∧
        (∀ k m : ℤ, -(L : ℤ) ≤ k → -(L : ℤ) ≤ m →
          F (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (k + d₁) *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) =
            ∑ i : Fin d₁, c₁ i *
              F (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (k + (i : ℕ)) *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) ∧
          F (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (m + d₂))) =
            ∑ i : Fin d₂, c₂ i *
              F (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (m + (i : ℕ))))) ∧
        ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ k m : ℤ, -(L : ℤ) ≤ k → -(L : ℤ) ≤ m →
          ‖F (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ k *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m))‖ ≤
            C * R ^ ((k + L).toNat + (m + L).toNat) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn.solution
