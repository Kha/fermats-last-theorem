import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_eq_comp_idelicNorm_of_isTwistedOrbitalIntegralOn_centralScalar_mul_of_isOrbitalIntegralOn_centralScalar_mul_of_areMatchingOn

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.eq_comp_idelicNorm_of_isTwistedOrbitalIntegralOn_centralScalar_mul_of_isOrbitalIntegralOn_centralScalar_mul_of_areMatchingOn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (c₀' : NNReal)
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hMatch : AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ μ
      (c₀' • adelicGLHaar (Fin 2) (𝓞 K) K) (φ ∘ AutomorphicForm.baseChangeGL K L) f)

    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (hy : AutomorphicForm.IsNormConjugator K L (AdeleRing (𝓞 K) K) σ γ δ y)
    (τK : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    [τK.IsHaarMeasure]
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)) [τ'.IsHaarMeasure]
    (hc : AutomorphicForm.Coupled K L (AdeleRing (𝓞 K) K) σ γ δ y τK τ')

    (IL : (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (hIL : ∀ w : (AdeleRing (𝓞 L) L)ˣ,
      AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ'
        ((fun g : GL (Fin 2) (AdeleRing (𝓞 L) L) => φ (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘
          AutomorphicForm.baseChangeGL K L) (IL w))
    (IK : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIK : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀' • adelicGLHaar (Fin 2) (𝓞 K) K) γ τK
        (fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (IK z)) :
    ∀ w : (AdeleRing (𝓞 L) L)ˣ,
      IL w = IK ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_eq_comp_idelicNorm_of_isTwistedOrbitalIntegralOn_centralScalar_mul_of_isOrbitalIntegralOn_centralScalar_mul_of_areMatchingOn.solution
