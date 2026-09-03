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
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_hasSum_torusShells_rsLocalIntegral22_jacquetIntegral_schwartz_of_integrable
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open IsDedekindDomain NumberField open AutomorphicForm hiding hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2 open LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.hasSum_torusShells_rsLocalIntegral22_jacquetIntegral_schwartz_of_integrable
    (p : HeightOneSpectrum (𝓞 ℚ))

    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (Φ₂ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∀ s : ℂ,

            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) →

            (∀ dn : ℤ × ℤ,
              IntegrableOn (fun k : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k)) ∂(selfDualHaarAt ℚ p)) *
                  w₂ (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k) *
                  Φ₂ ((ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0,
                    (ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))
                ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) μ₂) ∧

            Summable (fun dn : ℤ × ℤ =>
              ‖((((μN₂ ((fun y : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range =>
                    ((y : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹'
                    {z : p.adicCompletion ℚ | Valued.v z ≤ 1}))⁻¹).toReal : ℂ) *
                (Ideal.absNorm p.asIdeal : ℂ) ^ dn.1 *
                (((θ₀ ϖ : ℂˣ) : ℂ) * ((μ 0 ϖ : ℂˣ) : ℂ) * ((μ 1 ϖ : ℂˣ) : ℂ)) ^ dn.2 *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ (dn.1 + 2 * dn.2) *
                ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k)) ∂(selfDualHaarAt ℚ p)) *
                  w₂ (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k) *
                  Φ₂ ((ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0,
                    (ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂μ₂)‖) ∧

            HasSum (fun dn : ℤ × ℤ =>
              ((((μN₂ ((fun y : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range =>
                    ((y : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹'
                    {z : p.adicCompletion ℚ | Valued.v z ≤ 1}))⁻¹).toReal : ℂ) *
                (Ideal.absNorm p.asIdeal : ℂ) ^ dn.1 *
                (((θ₀ ϖ : ℂˣ) : ℂ) * ((μ 0 ϖ : ℂˣ) : ℂ) * ((μ 1 ϖ : ℂˣ) : ℂ)) ^ dn.2 *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ (dn.1 + 2 * dn.2) *
                ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k)) ∂(selfDualHaarAt ℚ p)) *
                  w₂ (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero dn.1 * k) *
                  Φ₂ ((ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0,
                    (ϖ : p.adicCompletion ℚ) ^ dn.2 * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂μ₂))
              (RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                (s + 1 / 2)
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_torusShells_rsLocalIntegral22_jacquetIntegral_schwartz_of_integrable.solution
