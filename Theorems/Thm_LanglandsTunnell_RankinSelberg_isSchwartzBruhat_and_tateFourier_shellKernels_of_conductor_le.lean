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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_isSchwartzBruhat_and_tateFourier_shellKernels_of_conductor_le
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.RankinSelberg.isSchwartzBruhat_and_tateFourier_shellKernels_of_conductor_le
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (ξ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (B : ℕ) (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ξ B)
    (f : ℕ)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hωf : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p f, ω u = 1)
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (b : ℕ) (hcθ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, θ₀ u = 1)
    (hBk : B < kp) (hfk : f ≤ kp) (hbk : 2 * b + 1 ≤ kp)
    (φ φ₁ : p.adicCompletion ℚ → ℂ)
    (hφdef : letI := LanglandsTunnell.TateLocal.localBorel ℚ p
      φ = (fun u : p.adicCompletion ℚ =>
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p)
          (fun x : p.adicCompletion ℚ => if Valued.v x = 1 then charExt (θ₀ * (χ * ξ⁻¹) ^ 2) x else 0) (-u)))
    (hφ₁def : φ₁ = (fun y : p.adicCompletion ℚ =>
        if Valued.v y = WithZero.exp (((2 * kp : ℕ)) : ℤ) then
          charExt ω⁻¹ (y * ((NumberField.AdelicLevel.uniformizerUnit ℚ p ^ (2 * kp) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ))
        else 0)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p
    IsSchwartzBruhat φ ∧ IsSchwartzBruhat φ₁ ∧

      (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 →
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ (t : p.adicCompletion ℚ) =
          (((θ₀ * (χ * ξ⁻¹) ^ 2) t : ℂˣ) : ℂ)) ∧
      (∀ y : p.adicCompletion ℚ, Valued.v y ≠ 1 →
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ y = 0) ∧

      (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 → ∀ y : p.adicCompletion ℚ,
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ ((t : p.adicCompletion ℚ) * y) =
          ((ω t : ℂˣ) : ℂ) * tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y) ∧
      (∀ y : p.adicCompletion ℚ, tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y ≠ 0 →
        Valued.v y ≤ WithZero.exp (-(f : ℤ))) ∧

      (∀ u y : p.adicCompletion ℚ, φ u ≠ 0 → φ₁ y ≠ 0 →
        y ≠ 0 ∧ Valued.v y⁻¹ ≤ WithZero.exp (-(f : ℤ)) ∧ Valued.v (y⁻¹ * u) ≤ WithZero.exp (-(f : ℤ)))  := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_isSchwartzBruhat_and_tateFourier_shellKernels_of_conductor_le.solution
