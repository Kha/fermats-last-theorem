import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_withDensity_norm_inv_preimage_mul_eq_and_lt_top_of_isCompact
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.withDensity_norm_inv_preimage_mul_eq_and_lt_top_of_isCompact
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    (∀ (g : (L ⊗[K] v.adicCompletion K)ˣ) (X : Set (L ⊗[K] v.adicCompletion K)), MeasurableSet X →
      ν.withDensity (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹)
          ((fun b : L ⊗[K] v.adicCompletion K => (g : L ⊗[K] v.adicCompletion K) * b) ⁻¹' X) =
        ν.withDensity (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹) X) ∧
    (∀ Q : Set (L ⊗[K] v.adicCompletion K), IsCompact Q → (∀ q ∈ Q, IsUnit q) →
      ν.withDensity (fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹) Q ≠ ∞) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_withDensity_norm_inv_preimage_mul_eq_and_lt_top_of_isCompact.solution
