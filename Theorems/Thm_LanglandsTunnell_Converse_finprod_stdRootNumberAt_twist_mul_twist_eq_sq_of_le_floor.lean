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

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_finprod_stdRootNumberAt_twist_mul_twist_eq_sq_of_le_floor
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.Converse.finprod_stdRootNumberAt_twist_mul_twist_eq_sq_of_le_floor
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : LanglandsTunnell.Converse.IsAdmissibleTwist K μ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (lam : ℂ)
    (b : ℕ)
    (hfloor : ∀ w ∈ primeFibre ℚ K p,
      2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w))
    (η₁A η₂A : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hη₁A : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ η₁A)
    (hη₂A : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ η₂A)
    (hη₁AN : LanglandsTunnell.Converse.IsAdmissibleTwist K
      (η₁A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm))
    (hη₂AN : LanglandsTunnell.Converse.IsAdmissibleTwist K
      (η₂A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm))
    (c₁ c₂ : ℕ)
    (hc₁ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar η₁A p) c₁)
    (hc₂ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar η₂A p) c₂)
    (hc₁b : c₁ ≤ b) (hc₂b : c₂ ≤ b) :
    ∀ s : ℂ,
      (lam *
      (∏ᶠ w ∈ primeFibre ℚ K p,
        ((NumberField.TateGlobal.localChar
          (η₁A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
      (∏ᶠ w ∈ primeFibre ℚ K p,
        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
            (NumberField.TateGlobal.localChar
              (η₁A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
            (LanglandsTunnell.Converse.pinnedExp K
                (η₁A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)))) *
      (lam *
      (∏ᶠ w ∈ primeFibre ℚ K p,
        ((NumberField.TateGlobal.localChar
          (η₂A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
      (∏ᶠ w ∈ primeFibre ℚ K p,
        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
            (NumberField.TateGlobal.localChar
              (η₂A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
            (LanglandsTunnell.Converse.pinnedExp K
                (η₂A.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)))) =
      (lam ^ 2 *
      ((∏ᶠ w ∈ primeFibre ℚ K p,
          ((NumberField.TateGlobal.localChar ((η₁A * η₂A).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
        ∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar μ w (-1) : ℂˣ) : ℂ)) *
      ((∏ᶠ w ∈ primeFibre ℚ K p,
          (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar ((η₁A * η₂A).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
            (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
              (LanglandsTunnell.Converse.pinnedExp K ((η₁A * η₂A).comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))) *
        ∏ᶠ w ∈ primeFibre ℚ K p,
          (LanglandsTunnell.TateLocal.stdRootNumberAt K w (NumberField.TateGlobal.localChar μ w) *
            (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
              (LanglandsTunnell.Converse.pinnedExp K μ w)))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_finprod_stdRootNumberAt_twist_mul_twist_eq_sq_of_le_floor.solution
