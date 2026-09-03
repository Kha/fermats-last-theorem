import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_AutomorphicForm_hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2
attribute [-instance] HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
open scoped ENNReal

theorem AutomorphicForm.hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ)) :
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion K)).range) [μN.IsHaarMeasure]
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ), Measurable f →
      (∀ x ∈ (unipotentGL2Hom (R := v.adicCompletion K)).range, ∀ g : GL (Fin 2) (v.adicCompletion K),
        f (x * g) = f g) →
      Integrable f (μ.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN)) →
      (∀ dn : ℤ × ℤ,
        IntegrableOn
          (fun k => f (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 *
            diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1 * k))
          ((AdelicDock.localLevelOne (𝓞 K) K v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion K))) :
            Set (GL (Fin 2) (v.adicCompletion K))) μ) ∧
      Summable (fun dn : ℤ × ℤ =>
        ((μN {x : ↥(unipotentGL2Hom (R := v.adicCompletion K)).range |
            (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1)⁻¹ *
              (x : GL (Fin 2) (v.adicCompletion K)) *
              (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1) ∈
            AdelicDock.localLevelOne (𝓞 K) K v ⊤})⁻¹).toReal *
          ∫ k in ((AdelicDock.localLevelOne (𝓞 K) K v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion K))) :
              Set (GL (Fin 2) (v.adicCompletion K))),
            ‖f (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 *
              diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1 * k)‖ ∂μ) ∧
      HasSum (fun dn : ℤ × ℤ =>
        (((μN {x : ↥(unipotentGL2Hom (R := v.adicCompletion K)).range |
            (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1)⁻¹ *
              (x : GL (Fin 2) (v.adicCompletion K)) *
              (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1) ∈
            AdelicDock.localLevelOne (𝓞 K) K v ⊤})⁻¹).toReal : ℂ) *
          ∫ k in ((AdelicDock.localLevelOne (𝓞 K) K v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion K))) :
              Set (GL (Fin 2) (v.adicCompletion K))),
            f (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 *
              diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1 * k) ∂μ)
        (∫ g, f g ∂(μ.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2.solution
