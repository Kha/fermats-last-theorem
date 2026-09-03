import Mathlib
import P2M.Util
namespace P2MW.S_NumberField_InfiniteAdeleRing_norm_algebraMap_apply_eq_and_prod_pow_mult_eq_norm

set_option autoImplicit false

open NumberField

theorem solution
    (K : Type) [Field K] [NumberField K] (x : K) :
    (∀ v : InfinitePlace K, ‖algebraMap K (InfiniteAdeleRing K) x v‖ = v x) ∧
    ∏ v : InfinitePlace K, v x ^ v.mult = ‖algebraMap K (InfiniteAdeleRing K) x‖ := by
  have h : ∀ v : InfinitePlace K, ‖algebraMap K (InfiniteAdeleRing K) x v‖ = v x := by
    intro v
    rw [NumberField.InfiniteAdeleRing.algebraMap_apply]
    exact UniformSpace.Completion.norm_coe _
  refine ⟨h, ?_⟩
  rw [NumberField.InfiniteAdeleRing.norm_def]
  exact Finset.prod_congr rfl fun v _ => by rw [h v]
