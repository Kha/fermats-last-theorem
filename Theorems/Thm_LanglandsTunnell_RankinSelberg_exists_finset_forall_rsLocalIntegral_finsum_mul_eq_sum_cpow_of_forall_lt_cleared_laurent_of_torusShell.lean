import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_finset_forall_rsLocalIntegral_finsum_mul_eq_sum_cpow_of_forall_lt_cleared_laurent_of_torusShell
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField open AutomorphicForm hiding hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2 open UnramifiedWhittaker LanglandsTunnell.TateLocal

theorem LanglandsTunnell.RankinSelberg.exists_finset_forall_rsLocalIntegral_finsum_mul_eq_sum_cpow_of_forall_lt_cleared_laurent_of_torusShell
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (F : ℤ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (B : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hF : ∀ i : ℤ, IsLocallyConstant (F i)) (hB : IsLocallyConstant B)
    (hFB : ∀ (i : ℤ) (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      F i (unipotent x * g) * B (unipotent x * g) = F i g * B g)
    (hFfin : ∀ C : Set (GL (Fin 2) (p.adicCompletion ℚ)), IsCompact C → {i : ℤ | ∃ g ∈ C, F i g ≠ 0}.Finite)
    (hcut : ∃ L : ℕ, ∀ (i : ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ n : ℤ × ℤ,
      (n.1 < -(L : ℤ) ∨ n.2 < -(L : ℤ)) →
        F i (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n.1 * k) = 0)

    (G : ℂ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (Gc : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hG : ∀ (u : ℂ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      G u g = ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * F i g)
    (hGc : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), Gc g = ∑ᶠ i : ℤ, F i g)

    (SQ : Finset (ℤ × ℤ)) (q : ℤ × ℤ → ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],

      (∃ u₀ : ℝ, ∀ u : ℝ, u₀ < u →
        ∃ (P : Polynomial ℂ) (m : ℤ) (σ : ℝ),
          (∀ s : ℂ, σ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (G u g * B g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (G u) B *
                (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))) →

      ∃ (M : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ),
        (∀ (u : ℂ) (s : ℂ),
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (G u g * B g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (G u) B *
              (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * u)) =
            ∑ mi ∈ M, c mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.2 : ℂ) * u) *
              (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.1 : ℂ) * s)) ∧
        (∀ s : ℂ,
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (Gc g * B g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s Gc B *
              (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s)) =
            ∑ mi ∈ M, c mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.1 : ℂ) * s)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_finset_forall_rsLocalIntegral_finsum_mul_eq_sum_cpow_of_forall_lt_cleared_laurent_of_torusShell.solution
