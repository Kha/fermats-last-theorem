import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure
import P2M.Util
import P2M.Sol.S_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] AutomorphicForm.glBorelOf

open scoped TensorProduct.RightActions in

theorem TwistedUnipotentTerm.isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ] [BorelSpace (L ⊗[K] v.adicCompletion K)ˣ]
    (μZ : Measure (L ⊗[K] v.adicCompletion K)ˣ) [μZ.IsHaarMeasure]
    (Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hΦ : AutomorphicForm.IsSemiLocalTestFn K L v Φ)
    (μT : Measure (L ⊗[K] v.adicCompletion K)ˣ) [IsFiniteMeasure μT]
    (C : Set (L ⊗[K] v.adicCompletion K)ˣ) (hC : IsCompact C) (hμTC : μT Cᶜ = 0) :
    IsLocallyConstant (fun y : L ⊗[K] v.adicCompletion K =>
        ∫ t : (L ⊗[K] v.adicCompletion K)ˣ, ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
          ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
            TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
              Φ (κ⁻¹ * TwistedUnipotentTerm.semiLocalUnipotent K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
                    L ⊗[K] v.adicCompletion K)) *
                  NumberField.AdelicLevel.diagOne
                    (Units.mapEquiv (Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv t * t⁻¹) *
                  TwistedUnipotentTerm.semiLocalCentral K L v
                    (Units.mapEquiv (Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) *
                  Matrix.GeneralLinearGroup.map
                    ((Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toRingHom) κ)
            ∂μZ ∂(AutomorphicForm.semiLocalHaar K L v) ∂μT) ∧
    HasCompactSupport (fun y : L ⊗[K] v.adicCompletion K =>
        ∫ t : (L ⊗[K] v.adicCompletion K)ˣ, ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
          ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
            TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
              Φ (κ⁻¹ * TwistedUnipotentTerm.semiLocalUnipotent K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
                    L ⊗[K] v.adicCompletion K)) *
                  NumberField.AdelicLevel.diagOne
                    (Units.mapEquiv (Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv t * t⁻¹) *
                  TwistedUnipotentTerm.semiLocalCentral K L v
                    (Units.mapEquiv (Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) *
                  Matrix.GeneralLinearGroup.map
                    ((Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toRingHom) κ)
            ∂μZ ∂(AutomorphicForm.semiLocalHaar K L v) ∂μT) := by p2m_exact_reverting @_root_.P2MW.S_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport.solution
