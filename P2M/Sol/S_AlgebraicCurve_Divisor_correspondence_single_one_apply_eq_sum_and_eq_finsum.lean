import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Divisor_correspondence_single_one_apply_eq_sum_and_eq_finsum

set_option autoImplicit false

open AlgebraicCurve Classical

namespace IdentB0

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)

open Classical in

theorem correspondence_single_one_apply (x y : Place K F) :
    Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ W ∈ Place.fiberAlong φ hφ x,
        if W.restrictAlong ψ hψ = y then
          (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0 := by
  classical
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Divisor.pushforwardAlong_single, Finsupp.single_apply, one_mul]
  all_goals (split_ifs <;> rfl)

open Classical in

theorem correspondence_single_one_apply_eq_finsum (x y : Place K F) :
    Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ᶠ W : Place K F',
        if W.restrictAlong φ hφ = x ∧ W.restrictAlong ψ hψ = y then
          (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0 := by
  classical
  rw [correspondence_single_one_apply]
  symm
  rw [finsum_eq_sum_of_support_subset _ (s := Place.fiberAlong φ hφ x)]
  · refine Finset.sum_congr rfl fun W hW => ?_
    rw [Place.mem_fiberAlong] at hW
    simp only [hW, true_and]
  · intro W hW
    rw [Function.mem_support] at hW
    simp only [Finset.mem_coe, Place.mem_fiberAlong]
    by_contra hx
    exact hW (if_neg fun h => hx h.1)

end Generic

end IdentB0

theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (x y : Place K F) :
    (Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ W ∈ Place.fiberAlong φ hφ x,
        if W.restrictAlong ψ hψ = y then (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0) ∧
    (Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ᶠ W : Place K F',
        if W.restrictAlong φ hφ = x ∧ W.restrictAlong ψ hψ = y then
          (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0) := by
  exact ⟨IdentB0.correspondence_single_one_apply φ ψ hφ hψ x y,
    IdentB0.correspondence_single_one_apply_eq_finsum φ ψ hφ hψ x y⟩
