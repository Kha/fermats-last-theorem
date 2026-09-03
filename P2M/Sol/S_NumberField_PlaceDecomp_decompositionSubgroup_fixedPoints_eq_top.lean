import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
namespace P2MW.S_NumberField_PlaceDecomp_decompositionSubgroup_fixedPoints_eq_top

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp Pointwise
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

theorem solution (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) [Finite (NumberField.PlaceDecomp.decomp E K w)] :
    (w.adicCompletionIntegers K).decompositionSubgroup (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  obtain ⟨σ, rfl⟩ := FixedPoints.toAlgAut_surjective (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K) f
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  show (MulSemiringAction.toAlgAut (NumberField.PlaceDecomp.decomp E K w)
      (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)) (w.adicCompletion K) σ⁻¹) x ∈
    w.adicCompletionIntegers K ↔ x ∈ w.adicCompletionIntegers K
  rw [MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply]
  exact NumberField.PlaceDecomp.smul_mem_adicCompletionIntegers_iff σ⁻¹ x
