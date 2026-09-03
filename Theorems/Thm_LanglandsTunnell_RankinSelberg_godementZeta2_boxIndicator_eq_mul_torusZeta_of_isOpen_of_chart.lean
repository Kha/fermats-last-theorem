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
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχc : IsLocallyConstant χ)
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hU : ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (L Mb Mc Md : ℤ) (hL : 0 ≤ L) (hMb : 0 ≤ Mb) (hMc : 0 ≤ Mc) (hMd : 1 ≤ Md)
    (hsupp : ∀ y : (p.adicCompletion ℚ)ˣ, WithZero.exp L < Valued.v (y : p.adicCompletion ℚ) → w (diagOne y) = 0)
    (hstab : ∀ (a : (p.adicCompletion ℚ)ˣ) (y : p.adicCompletion ℚ),
      Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → Valued.v y ≤ WithZero.exp (-Mc) →
        diagUnits2 1 a * lowerUnipotentGL2 y ∈ U)
    (hχ : ∀ a : (p.adicCompletion ℚ)ˣ, Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → χ a = 1)
    (Φ₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hΦ₀ : Φ₀ = fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
        Set.indicator {X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) |
            Valued.v (X 0 0) ≤ WithZero.exp L ∧ Valued.v (X 0 1) ≤ WithZero.exp (-Mb) ∧
            Valued.v (X 1 0) ≤ WithZero.exp (-Mc) ∧ Valued.v (X 1 1 - 1) ≤ WithZero.exp (-Md)} (fun _ => (1 : ℂ)) X) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (c : ENNReal), c ≠ 0 → c ≠ ⊤ →
      μ₂ = c • Measure.map
          (fun q : (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ) =>
            unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2)
          ((((selfDualHaarAt ℚ p).prod ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (selfDualHaarAt ℚ p))))).withDensity fun q =>
            (modulus (((q.2.1 * (q.2.2.1)⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) : ENNReal)) →
      (((c.toReal : ℝ) : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mb)}).toReal : ℂ) *
            (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {a : (p.adicCompletion ℚ)ˣ | Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md)}).toReal : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mc)}).toReal : ℂ)) ≠ 0 ∧
      ∀ s : ℂ,
        Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
          w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          w g * Φ₀ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂ ∧
        godementZeta2 p μ₂ w Φ₀ χ (s + 1 / 2) =
          (((c.toReal : ℝ) : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mb)}).toReal : ℂ) *
            (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {a : (p.adicCompletion ℚ)ˣ | Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md)}).toReal : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mc)}).toReal : ℂ)) *
            ∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart.solution
