import Mathlib
import P2M.Util
namespace P2MW.S_AbsoluteValue_Completion_norm_coe_and_exists_one_lt_norm

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

theorem solution
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    (∀ x : K, ‖(x : v.Completion)‖ = v x) ∧ (v.IsNontrivial → ∃ x : v.Completion, 1 < ‖x‖) := by
  have h : ∀ x : K, ‖(x : v.Completion)‖ = v x := fun x => by
    rw [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs]
  refine ⟨h, fun hnt => ?_⟩
  obtain ⟨x, hx⟩ := hnt.exists_abv_gt_one
  exact ⟨x, by rwa [h]⟩

