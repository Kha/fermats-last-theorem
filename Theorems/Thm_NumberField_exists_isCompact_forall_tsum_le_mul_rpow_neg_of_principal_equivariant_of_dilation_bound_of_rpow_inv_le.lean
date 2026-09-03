import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import P2M.Util
import P2M.Sol.S_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound_of_rpow_inv_le
attribute [-instance] instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped NNReal

open scoped Classical in

theorem NumberField.exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound_of_rpow_inv_le
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (Y : Set (AdeleRing (𝓞 F) F)ˣ), IsCompact Y →
      ∃ U' : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact U' ∧
        ∀ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (σ₁ σ₂ c' : ℝ) (N : ℕ), 0 < c' →
          ∃ Nd : ℕ, ∀ c : ℝ, ∃ M : ℝ,
            ∀ (G : {ξ : F // ξ ≠ 0} → (AdeleRing (𝓞 F) F)ˣ → ℝ) (σ : ℝ), σ₁ ≤ σ → σ ≤ σ₂ →
              (∀ ξ y, 0 ≤ G ξ y) →
              (∀ (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (y : (AdeleRing (𝓞 F) F)ˣ),
                G ξ (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
                  = G ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ y) →
              (∀ u ∈ U', ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), c' ^ ((Module.finrank ℚ F : ℝ)⁻¹) ≤ r →
                (z : AdeleRing (𝓞 F) F).2 = 1 →
                (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
                ∀ ξ : {ξ : F // ξ ≠ 0},
                  ((ξ : F) ∉ I → G ξ (z * u) = 0) ∧
                  G ξ (z * u) ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - σ)) *
                    (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                    (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(Nd : ℝ))) *
                    ∏ w : {w : InfinitePlace F // w.IsComplex},
                      (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * Nd : ℝ))) →
              ∀ (y₁ y₀ : (AdeleRing (𝓞 F) F)ˣ), y₀ ∈ Y → c' ≤ ((α y₁ : ℝˣ) : ℝ) →
                Summable (fun ξ : {ξ : F // ξ ≠ 0} => G ξ (y₁ * y₀)) ∧
                ∑' ξ : {ξ : F // ξ ≠ 0}, G ξ (y₁ * y₀) ≤ M * ((α y₁ : ℝˣ) : ℝ) ^ (-(N : ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound_of_rpow_inv_le.solution
