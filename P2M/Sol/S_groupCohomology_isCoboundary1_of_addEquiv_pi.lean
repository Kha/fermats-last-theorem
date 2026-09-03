import Mathlib
import P2M.Util
namespace P2MW.S_groupCohomology_isCoboundary1_of_addEquiv_pi

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
open groupCohomology

theorem solution
    {G P P₀ : Type*} [Group G] [AddCommGroup P] [AddCommGroup P₀] [SMul G P]
    (e : P ≃+ (G → P₀)) (he : ∀ (h : G) (p : P) (x : G), e (h • p) x = e p (h⁻¹ * x))
    (f : G → P) (hf : IsCocycle₁ f) : IsCoboundary₁ f := by

  refine ⟨e.symm (fun x => e (f x⁻¹) 1), fun g => ?_⟩
  apply e.injective
  funext x
  rw [map_sub, e.apply_symm_apply, Pi.sub_apply, he, e.apply_symm_apply, mul_inv_rev, inv_inv]

  rw [hf x⁻¹ g, map_add, Pi.add_apply, he, inv_inv, mul_one, add_sub_cancel_right]
