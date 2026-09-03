import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (α β : (L ⊗[K] v.adicCompletion K)ˣ) (a b : (v.adicCompletion K)ˣ), a ≠ b →
        AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) →
        ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
            (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
          @Measure.IsHaarMeasure _ _ _
            (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
          τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
        ∀ βs : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) → ℝ, Measurable βs → (∀ p, 0 ≤ βs p) →
          (∀ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K), IsUnit p.1 → IsUnit p.2 →
            @integral _ ℝ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ'
              (fun t => βs ((((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) * p.1,
                (((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) * p.2)) = 1) →
        ∀ c : ℝ, ∀ J' I' : ℂ,
          AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
          AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ I' →
          Integrable (fun p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K) =>
              (if h : IsUnit p.1 ∧ IsUnit p.2 then
                ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
                  ∫ ξ : (L ⊗[K] v.adicCompletion K),
                    (∫ k in AutomorphicForm.semiLocalIntegralSet K L v, φ (k⁻¹ * (diagUnits2 (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹) (β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) *
                      AutomorphicForm.unipotentGL2 (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ ξ -
                        (((β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) * (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * ξ)) *
                    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ k)
                      ∂(AutomorphicForm.semiLocalHaar K L v)) *
                    ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ) ∂ν
               else 0)) (ν.prod ν) ∧
          J' + (c : ℂ) * I' = (κ : ℂ) * ∫ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
              (if h : IsUnit p.1 ∧ IsUnit p.2 then
                ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) * (βs p : ℂ) *
                  ∫ ξ : (L ⊗[K] v.adicCompletion K),
                    (∫ k in AutomorphicForm.semiLocalIntegralSet K L v, φ (k⁻¹ * (diagUnits2 (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹) (β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) *
                      AutomorphicForm.unipotentGL2 (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ ξ -
                        (((β * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.2.unit * h.2.unit⁻¹) * (α * (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : (L ⊗[K] v.adicCompletion K) →* (L ⊗[K] v.adicCompletion K))) h.1.unit * h.1.unit⁻¹)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * ξ)) *
                    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ k)
                      ∂(AutomorphicForm.semiLocalHaar K L v)) *
                    ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 ξ) + c : ℝ) : ℂ) ∂ν
               else 0) ∂(ν.prod ν) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.solution
