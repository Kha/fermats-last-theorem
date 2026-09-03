import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
  LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)

    (Kb₁ Kb₂ : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hKb₁ : IsOpen (Kb₁ : Set (GL (Fin 2) (v.adicCompletion K))))
    (hKb₁K : Kb₁ ≤ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
    (hKb₁c : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
        - 1) i j) ≤ WithZero.exp (-(b : ℤ))) → k ∈ Kb₁)
    (hKb₂ : IsOpen (Kb₂ : Set (GL (Fin 2) (v.adicCompletion K))))
    (hKb₂K : Kb₂ ≤ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
    (hKb₂c : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
        - 1) i j) ≤ WithZero.exp (-(b : ℤ))) → k ∈ Kb₂)

    (A₁ A₂ : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hA₁ : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion K)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (v.adicCompletion K), A₁ (g * k) = A₁ g)
    (hA₂ : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion K)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (v.adicCompletion K), A₂ (g * k) = A₂ g)

    (E₁ E₂ : ℤ → GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hE₁K : ∀ i : ℤ, ∀ k ∈ Kb₁, ∀ g : GL (Fin 2) (v.adicCompletion K), E₁ i (g * k) = E₁ i g)
    (hE₂K : ∀ i : ℤ, ∀ k ∈ Kb₂, ∀ g : GL (Fin 2) (v.adicCompletion K), E₂ i (g * k) = E₂ i g)
    (hAE₁ : ∀ (i : ℤ) (x : v.adicCompletion K) (g : GL (Fin 2) (v.adicCompletion K)),
      A₁ (unipotent x * g) * E₁ i (unipotent x * g) = A₁ g * E₁ i g)
    (hAE₂ : ∀ (i : ℤ) (x : v.adicCompletion K) (g : GL (Fin 2) (v.adicCompletion K)),
      A₂ (unipotent x * g) * E₂ i (unipotent x * g) = A₂ g * E₂ i g)
    (hE₁fin : ∀ C : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact C →
      {i : ℤ | ∃ g ∈ C, E₁ i g ≠ 0}.Finite)
    (hE₂fin : ∀ C : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact C →
      {i : ℤ | ∃ g ∈ C, E₂ i g ≠ 0}.Finite)

    (w₁ w₂ : ℂ → GL (Fin 2) (v.adicCompletion K) → ℂ) (wc₁ wc₂ : GL (Fin 2) (v.adicCompletion K) → ℂ) (u₁ : ℝ)
    (hw₁ : ∀ u : ℂ, u₁ < u.re → ∀ g : GL (Fin 2) (v.adicCompletion K),
      w₁ u g = ∑ᶠ i : ℤ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E₁ i g)
    (hw₂ : ∀ u : ℂ, u₁ < u.re → ∀ g : GL (Fin 2) (v.adicCompletion K),
      w₂ u g = ∑ᶠ i : ℤ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E₂ i g)
    (hwc₁ : ∀ g : GL (Fin 2) (v.adicCompletion K), wc₁ g = ∑ᶠ i : ℤ, E₁ i g)
    (hwc₂ : ∀ g : GL (Fin 2) (v.adicCompletion K), wc₂ g = ∑ᶠ i : ℤ, E₂ i g)

    (γ : ℂ → ℂ) (e : ℤ) :
    letI := localBorel K v
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := v.adicCompletion K)).range) [μN₂.IsHaarMeasure]
      (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure],

      (∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤, ∀ (η : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ),
        HasConductorExponentAt K v η c → c ≤ b →
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
              (∫ k in ((Kb₁ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
                  A₁ (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν) = 0) →
      (∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤, ∀ (η : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ),
        HasConductorExponentAt K v η c → c ≤ b →
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
              (∫ k in ((Kb₂ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
                  A₂ (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν) = 0) →

      (∃ u₀ : ℝ, ∀ u : ℂ, u₀ < u.re →
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A₁ g * w₁ u g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A₂ g * w₂ u g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) ∧
          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
                (fun g : GL (Fin 2) (v.adicCompletion K) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
                s A₁ (w₁ u) =
              (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
                (fun g : GL (Fin 2) (v.adicCompletion K) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
                s A₂ (w₂ u) =
              (Ideal.absNorm v.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ,
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
              (γ s * (Ideal.absNorm v.asIdeal : ℂ) ^ ((e : ℂ) * u)) *
                ((Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ s)))) →

      (∃ σc : ℝ, ∀ s : ℂ, σc < s.re →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A₁ g * wc₁ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂)) ∧
          Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A₂ g * wc₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) →

      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
        (∀ s : ℂ, σ₂ < s.re →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
            (A₁ g * wc₁ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
              v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
            (A₂ g * wc₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
              v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) ∧
        (∀ s : ℂ, σ₂ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
              (fun g : GL (Fin 2) (v.adicCompletion K) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
              s A₁ wc₁ =
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
              (fun g : GL (Fin 2) (v.adicCompletion K) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
              s A₂ wc₂ =
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            γ s * ((Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ s))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell.solution
