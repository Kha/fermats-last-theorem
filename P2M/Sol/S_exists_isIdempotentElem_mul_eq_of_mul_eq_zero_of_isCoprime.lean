import Mathlib
import P2M.Util
namespace P2MW.S_exists_isIdempotentElem_mul_eq_of_mul_eq_zero_of_isCoprime

set_option autoImplicit false

universe u

theorem solution
    {R : Type u} [CommRing R] {f g : R} (hfg : f * g = 0) (hcop : IsCoprime f g) :
    ∃ e w : R, IsIdempotentElem e ∧ IsUnit w ∧ f = e * w := by
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : f * (u * f) = f := by linear_combination (-v) * hfg + f * huv
  refine ⟨u * f, f + (1 - u * f), ?_, ?_, ?_⟩
  · show u * f * (u * f) = u * f
    linear_combination (-(u * v)) * hfg + (u * f) * huv
  · exact isUnit_iff_exists_inv.mpr ⟨u * (u * f) + (1 - u * f), by linear_combination (2 * u - u ^ 2 - 1) * h1⟩
  · linear_combination (u - 1) * h1
