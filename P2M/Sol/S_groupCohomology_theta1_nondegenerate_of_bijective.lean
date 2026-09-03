import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
namespace P2MW.S_groupCohomology_theta1_nondegenerate_of_bijective
set_option autoImplicit false
open Module groupCohomology
universe u

theorem solution {k G : Type u} [Group G] [Field k]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M D : Rep.{u} k G}
    (θ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D))
    (hbij : Function.Bijective θ) :
    (∀ x : continuousH1 r M, (∀ w : continuousH1 r D, θ x w = 0) → x = 0)
    ∧ ∀ w : continuousH1 r D, (∀ x : continuousH1 r M, θ x w = 0) → w = 0 := by
  constructor
  · intro x hx
    apply hbij.injective
    rw [map_zero]
    ext w
    exact hx w
  · intro w hw
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro f
    obtain ⟨x, rfl⟩ := hbij.surjective f
    exact hw x
