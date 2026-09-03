import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_mul_localZeta_rational_and_clearedFE
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_mul_localZeta_rational_and_clearedFE
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ ν : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hμ : IsLocallyConstant μ) (hν : IsLocallyConstant ν) :
    letI := localBorel ℚ p
    ∃ (Γn Γd : Polynomial ℂ) (eΓ : ℤ), Γn ≠ 0 ∧ Γd ≠ 0 ∧
      ∀ (φ₁ φ₂ : p.adicCompletion ℚ → ℂ), IsSchwartzBruhat φ₁ → IsSchwartzBruhat φ₂ →
        ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧

          (∀ s : ℂ, σ < s.re →
            Integrable (fun a : (p.adicCompletion ℚ)ˣ =>
              φ₁ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s)
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
            Integrable (fun d : (p.adicCompletion ℚ)ˣ =>
              φ₂ (d : p.adicCompletion ℚ) * ((ν d : ℂˣ) : ℂ) * ((modulus (d : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s)
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
            (∫ a : (p.adicCompletion ℚ)ˣ,
                φ₁ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
              (∫ d : (p.adicCompletion ℚ)ˣ,
                φ₂ (d : p.adicCompletion ℚ) * ((ν d : ℂˣ) : ℂ) * ((modulus (d : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ, σd < s.re →
            Integrable (fun a : (p.adicCompletion ℚ)ˣ =>
              tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ₁ (a : p.adicCompletion ℚ) *
                ((μ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s))
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
            Integrable (fun d : (p.adicCompletion ℚ)ˣ =>
              tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ₂ (d : p.adicCompletion ℚ) *
                ((ν⁻¹ d : ℂˣ) : ℂ) * ((modulus (d : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s))
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
            (∫ a : (p.adicCompletion ℚ)ˣ,
                tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ₁ (a : p.adicCompletion ℚ) *
                  ((μ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
              (∫ d : (p.adicCompletion ℚ)ˣ,
                tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ₂ (d : p.adicCompletion ℚ) *
                  ((ν⁻¹ d : ℂˣ) : ℂ) * ((modulus (d : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ,
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) *
                Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * Γd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Γn.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((eΓ : ℂ) * s) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_mul_localZeta_rational_and_clearedFE.solution
