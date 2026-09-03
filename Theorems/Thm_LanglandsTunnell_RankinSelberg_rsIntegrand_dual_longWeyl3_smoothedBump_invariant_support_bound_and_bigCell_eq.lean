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
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical in

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (ω θ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (f : ℕ)
    (W₀ : LocalGL3 p → ℂ)
    (hW₀law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀)
    (hW₀sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (hω : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₀ h)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (hbumpK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL (h * k)) = W₀ (iotaGL h))
    (hbumpS : ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
      ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k)
    (hbump1 : W₀ (iotaGL 1) = 1)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hθ : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ z : ℂˣ) : ℂ) * w g)
    (φ φ₁ : p.adicCompletion ℚ → ℂ) (hφ : IsSchwartzBruhat φ) (hφ₁ : IsSchwartzBruhat φ₁) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI := localBorel ℚ p

    (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 → tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ (t : p.adicCompletion ℚ) = ((θ t : ℂˣ) : ℂ)) →
    (∀ y : p.adicCompletion ℚ, Valued.v y ≠ 1 → tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ y = 0) →
    (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 → ∀ y : p.adicCompletion ℚ,
      tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ ((t : p.adicCompletion ℚ) * y) = ((ω t : ℂˣ) : ℂ) * tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y) →
    (∀ y : p.adicCompletion ℚ, tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y ≠ 0 → Valued.v y ≤ WithZero.exp (-(f : ℤ))) →

    Measurable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g))) ∧

    (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL (unipotent x * g)) *
          (((modulus ((Matrix.GeneralLinearGroup.det (unipotent x * g) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) (unipotent x * g))) =
        dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g))) ∧

    (∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g)) ≠ 0 →
        ∃ (x : p.adicCompletion ℚ) (u : GL (Fin 2) (p.adicCompletion ℚ)),
          u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ∧ g = unipotent x * u) ∧

    (∃ C : ℝ, ∀ g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ‖dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g))‖ ≤ C) ∧

    (∀ (y x : p.adicCompletion ℚ) (a d : (p.adicCompletion ℚ)ˣ),
        (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))).indicator
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g)))
          (unipotentGL2 y * diagUnits2 d a * lowerUnipotentGL2 x) =
        (if Valued.v y ≤ 1 then (1 : ℂ) else 0) *
          (if Valued.v (a : p.adicCompletion ℚ) = 1 ∧ Valued.v (d : p.adicCompletion ℚ) = 1 then
            ((ω (a * d⁻¹) : ℂˣ) : ℂ) * tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ x *
              w (w₀p * diagUnitGL2 (a * d⁻¹) * unipotent (-x))
          else 0)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq.solution
