import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_setIntegral_twistedHyperbolicCell_self_one_eq_setIntegral_hyperbolicCell

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.setIntegral_twistedHyperbolicCell_self_one_eq_setIntegral_hyperbolicCell
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (Φ₁ Φ₂ : Set (AdelicGL2 (𝓞 K) K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) K K)
    (hgen : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    ∀ R : ℝ,
      ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
        (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ {δ : GL (Fin 2) K | ∃ γ : GL (Fin 2) K,
              γ ∈ AutomorphicForm.hyperbolicCell K ∧
              LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk (1 : K ≃ₐ[K] K) δ) = ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K δ *
                AutomorphicForm.sigmaAdelicAct K K D 1 (AutomorphicForm.centralScalar (𝓞 K) K z * x))) -
          Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
          (@AutomorphicForm.constantTerm _
            (productionPinsOf K Φ₁ (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
              (fun w => heckeGen (𝓞 K) K w) (adelicBox K)).nS _ _
            (productionPinsOf K Φ₁ (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
              (fun w => heckeGen (𝓞 K) K w) (adelicBox K)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) K |
              (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K δ * AutomorphicForm.sigmaAdelicAct K K D 1 y)))
          (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
        (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              (AutomorphicForm.adelicKernelHyperbolicPart K φ x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf K Φ₂ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                  (productionPinsOf K Φ₂ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                    (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_setIntegral_twistedHyperbolicCell_self_one_eq_setIntegral_hyperbolicCell.solution
