import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_NumberField_PlaceDecomp_decompositionSubgroup_fixedPoints_eq_top
import P2M.Util
namespace P2MW.S_NumberField_PlaceDecomp_exists_mulEquiv_decompositionSubgroup_fixedPoints

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp Pointwise
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

theorem solution (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) [Finite (NumberField.PlaceDecomp.decomp E K w)] :
    ∃ Φ : NumberField.PlaceDecomp.decomp E K w ≃*
        ((w.adicCompletionIntegers K).decompositionSubgroup (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K))),
      ∀ (σ : NumberField.PlaceDecomp.decomp E K w) (x : w.adicCompletion K),
        ((Φ σ : (w.adicCompletion K) ≃ₐ[FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)] (w.adicCompletion K)) : _) x = σ • x := by
  classical
  haveI := NumberField.PlaceDecomp.faithfulSMul_decomp E K w
  let Φ₁ := FixedPoints.toAlgAutMulEquiv (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)
  let Φ₂ : ((w.adicCompletion K) ≃ₐ[FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)] (w.adicCompletion K)) ≃*
      ((w.adicCompletionIntegers K).decompositionSubgroup (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K))) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr (NumberField.PlaceDecomp.decompositionSubgroup_fixedPoints_eq_top E K w).symm)
  refine ⟨Φ₁.trans Φ₂, fun σ x => ?_⟩
  show (MulSemiringAction.toAlgAut (NumberField.PlaceDecomp.decomp E K w)
      (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)) (w.adicCompletion K) σ) x = σ • x
  rw [MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply]
