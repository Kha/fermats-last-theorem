import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Theorems.Thm_NumberField_PlaceDecomp_smul_algebraMap
import P2M.Util
namespace P2MW.S_NumberField_PlaceDecomp_faithfulSMul_decomp

set_option autoImplicit false
open scoped NumberField.PlaceDecomp

theorem solution (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FaithfulSMul (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K) := by
  refine ⟨fun {σ τ} h => Subtype.ext (AlgEquiv.ext fun k => ?_)⟩
  apply (algebraMap K (w.adicCompletion K)).injective
  rw [← NumberField.PlaceDecomp.smul_algebraMap, ← NumberField.PlaceDecomp.smul_algebraMap]
  exact h _
