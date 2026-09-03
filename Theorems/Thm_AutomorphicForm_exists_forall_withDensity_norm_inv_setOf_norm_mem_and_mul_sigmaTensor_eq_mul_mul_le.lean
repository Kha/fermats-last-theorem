import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_withDensity_norm_inv_setOf_norm_mem_and_mul_sigmaTensor_eq_mul_mul_le
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_forall_withDensity_norm_inv_setOf_norm_mem_and_mul_sigmaTensor_eq_mul_mul_le
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (W : Set (v.adicCompletion K)) (hW : IsCompact W) (hW0 : (0 : v.adicCompletion K) ∉ W)
    (U : Set (L ⊗[K] v.adicCompletion K)) (hU : IsCompact U) (hU1 : ∀ u ∈ U, IsUnit u) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (A : (L ⊗[K] v.adicCompletion K)ˣ) (p : L ⊗[K] v.adicCompletion K),
      ν.withDensity (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹)
        {b : L ⊗[K] v.adicCompletion K | IsUnit b ∧ Algebra.norm (v.adicCompletion K) b ∈ W ∧
          ∃ u ∈ U, (A : L ⊗[K] v.adicCompletion K) * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ b =
            b * p * u} ≤ C := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_withDensity_norm_inv_setOf_norm_mem_and_mul_sigmaTensor_eq_mul_mul_le.solution
