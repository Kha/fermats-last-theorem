import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_map_sigmaTensor_sub_mul_eq_inv_nnnorm_one_sub_norm_smul
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct
open LanglandsTunnell.CubicInduction (diagUnits2)
open MeasureTheory
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.map_sigmaTensor_sub_mul_eq_inv_nnnorm_one_sub_norm_smul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (r : (L ⊗[K] v.adicCompletion K)) (hr : Algebra.norm (v.adicCompletion K) r ≠ 1) :
    Measure.map (fun y : (L ⊗[K] v.adicCompletion K) => AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ y - r * y) ν =
      ((‖(1 : (v.adicCompletion K)) - Algebra.norm (v.adicCompletion K) r‖₊)⁻¹ : NNReal) • ν := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_map_sigmaTensor_sub_mul_eq_inv_nnnorm_one_sub_norm_smul.solution
