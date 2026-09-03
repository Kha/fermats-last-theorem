import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (Z : Set (L ⊗[K] v.adicCompletion K)) (hZ : IsCompact Z)
    (Qc : Set (L ⊗[K] v.adicCompletion K)ˣ) (hQc : IsCompact Qc) :
    IntegrableOn (fun z : (L ⊗[K] v.adicCompletion K) => Real.log ‖Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z‖) Z ν ∧
    ∃ C : ℝ, ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ),
      ∀ u : (v.adicCompletion K)ˣ, u ∈ U → u ^ Module.finrank K L ≠ 1 → ∀ q : (L ⊗[K] v.adicCompletion K)ˣ, q ∈ Qc →
      ∀ g : (L ⊗[K] v.adicCompletion K) → ℂ, Measurable g → (∀ z, ‖g z‖ ≤ 1) → (∀ z, z ∉ Z → g z = 0) →
        ‖(‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ : ℂ) *
            ∫ η : (L ⊗[K] v.adicCompletion K), g (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ η -
                (Algebra.TensorProduct.includeRight (R := K) (A := L) (u : (v.adicCompletion K)) : (L ⊗[K] v.adicCompletion K)) * η) *
              ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 (((q : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * η)) +
                  2 * (Module.finrank K L : ℝ) * Real.log ‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ : ℝ) : ℂ) ∂ν -
          ∫ z : (L ⊗[K] v.adicCompletion K), g z *
              ((2 * Real.log ‖Algebra.norm (v.adicCompletion K) (((q : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)))‖ +
                  2 * (Module.finrank K L : ℝ) * Real.log ‖Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z‖ : ℝ) : ℂ) ∂ν‖ ≤
          C * ‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖|) ∧
        (‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ : ℂ) * ∫ η : (L ⊗[K] v.adicCompletion K), g (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ η -
                (Algebra.TensorProduct.includeRight (R := K) (A := L) (u : (v.adicCompletion K)) : (L ⊗[K] v.adicCompletion K)) * η) ∂ν = ∫ z : (L ⊗[K] v.adicCompletion K), g z ∂ν := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le.solution
