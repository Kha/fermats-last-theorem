import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure
import P2M.Util
import P2M.Sol.S_TwistedUnipotentTerm_setIntegral_integral_semiLocalCharacter_mul_wordIndicator_twist_eq_of_mem_integralUnits

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] AutomorphicForm.glBorelOf

open scoped TensorProduct.RightActions in
theorem TwistedUnipotentTerm.setIntegral_integral_semiLocalCharacter_mul_wordIndicator_twist_eq_of_mem_integralUnits
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L)) (z : GL (Fin 2) (w.1.adicCompletion L))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ] [BorelSpace (L ⊗[K] v.adicCompletion K)ˣ]
    (μZ : Measure (L ⊗[K] v.adicCompletion K)ˣ) [μZ.IsHaarMeasure]
    (hξσ : ∀ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v
        (Units.mapEquiv (Algebra.TensorProduct.congr σ
          (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) =
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ)
    (t : (L ⊗[K] v.adicCompletion K)ˣ) (ht : t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v)
    (k j : ℕ) (y : L ⊗[K] v.adicCompletion K) :
    ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v, ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
        TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
          TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
            (κ⁻¹ * TwistedUnipotentTerm.semiLocalUnipotent K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
                L ⊗[K] v.adicCompletion K)) *
              NumberField.AdelicLevel.diagOne
                (Units.mapEquiv (Algebra.TensorProduct.congr σ
                  (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv t * t⁻¹) *
              TwistedUnipotentTerm.semiLocalCentral K L v
                (Units.mapEquiv (Algebra.TensorProduct.congr σ
                  (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) *
              Matrix.GeneralLinearGroup.map
                ((Algebra.TensorProduct.congr σ
                  (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toRingHom) κ) ∂μZ
      ∂(AutomorphicForm.semiLocalHaar K L v) =
    ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v, ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
        TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
          TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
            (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v y) ∂μZ
      ∂(AutomorphicForm.semiLocalHaar K L v) := by p2m_exact_reverting @_root_.P2MW.S_TwistedUnipotentTerm_setIntegral_integral_semiLocalCharacter_mul_wordIndicator_twist_eq_of_mem_integralUnits.solution
