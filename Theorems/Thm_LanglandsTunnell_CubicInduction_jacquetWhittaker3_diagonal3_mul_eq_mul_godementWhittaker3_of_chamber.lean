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
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ), ‖((lam i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0) (h12 : σ 2 < σ 1)
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (T : LocalGL3 p) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p

    ∃ (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) (R : ℝ), IsOpen U ∧ (1 : GL (Fin 2) (p.adicCompletion ℚ)) ∈ U ∧
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →

    ∀ (φsec : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (φsec = fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)) =>
        let Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))
        let s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := Matrix.of fun i j => Z i (Fin.castSucc j)
        let N : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z
        ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
          (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) *
          (Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).indicator (fun _ => (1 : ℂ)) s *
          (charExt (lam 0) s.det)⁻¹ * ((‖s.det‖⁻¹ : ℝ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ) *
          charExt (lam 1) (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * s.det / N 1 0) *
          charExt (lam 2) (N 1 0) * ((‖N 1 0‖⁻¹ : ℝ) : ℂ) *
          Φ ![N 1 1 / N 1 0, N 1 2 / N 1 0, (Z 0 0 * Z 1 2 - Z 0 2 * Z 1 0) / s.det]) →

    ∀ (𝔇 : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (𝔇 = fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
        ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
          φsec X (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)) →

    (∀ g : LocalGL3 p,
      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          rowFourier23 p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹⁻¹
              (fun X => 𝔇 (X * ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹)
              (godementArg p h) *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ)) μ₂ ∧
      jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * g * T) =
        ((lam 1 (-1) : ℂˣ) : ℂ) *
          godementWhittaker3 p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ μ₂ (lam 0) 𝔇 g) ∧

    HasCompactSupport 𝔇 ∧
    (∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)), 𝔇 X k ≠ 0 →
      (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j)) ∈
        Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))) ∧

    (∀ X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ),
      φsec X ∈ principalSeries2 p ![lam 1, lam 2] ∧
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φsec X g ≠ 0 →
        ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 0 ≠ 0 ∧
        ‖((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 1‖ ≤
          R * ‖((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 0‖) ∧

    ((K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ⊆ U →
      ∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), φsec X g ≠ 0 →
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ≠ 0 ∧
          ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ≤
            R * ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖) ∧

    (∃ (m : ℕ) (φ₁ : Fin m → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ)
        (φ₂ : Fin m → (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ)
        (φ : Fin m → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ i, IsLocallyConstant (φ₁ i) ∧ HasCompactSupport (φ₁ i)) ∧
      (∀ i, IsLocallyConstant (φ₂ i) ∧ HasCompactSupport (φ₂ i)) ∧
      (∀ i, φ i ∈ principalSeries2 p ![lam 1, lam 2] ∧
        ∃ s ∈ K, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φ i g ≠ 0 →
          ((g * s : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ≠ 0) ∧
      (∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)),
        𝔇 X k = ∑ i, φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
          ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            φ i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)) ∧

      ∀ g : LocalGL3 p,
        (∀ i, Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            rowFourier23 p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹⁻¹
                (fun X => (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
              φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
                ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))
                  (X * ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹)
                (godementArg p h) *
              ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
                ^ (1 / 2 : ℂ)) μ₂) ∧
        jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * g * T) =
          ((lam 1 (-1) : ℂˣ) : ℂ) *
            ∑ i, godementWhittaker3 p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ μ₂ (lam 0)
              (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
              φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
                ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)) g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber.solution
