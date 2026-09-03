import Mathlib
import P2M.Util
import P2M.Sol.S_AnnulusSlope_sum_sum_mul_slopeDrop_smul_add_sum_slope_smul_eq_zero

set_option autoImplicit false

universe u v

open Finset BigOperators

theorem AnnulusSlope.sum_sum_mul_slopeDrop_smul_add_sum_slope_smul_eq_zero
    {S : Type u} [Fintype S] {M : Type v} [AddCommGroup M]
    (coord : S → M) (v : M) (e : S → ℕ) (he : ∀ s, 1 ≤ e s)
    (hv : ∀ s, (e s : ℤ) • coord s = v) (hsum : ∑ s, coord s = 0)
    (g : S → ℕ → ℤ) (δ : ℤ) (hδ : ∀ s, g s (e s) - g s 0 = δ) :
    ∑ s, (∑ d ∈ Finset.Ico 1 (e s),
        (d : ℤ) * ((g s d - g s (d - 1)) - (g s (d + 1) - g s d))) • coord s +
      (∑ s, (g s (e s) - g s (e s - 1))) • v = 0 := by p2m_exact_reverting @_root_.P2MW.S_AnnulusSlope_sum_sum_mul_slopeDrop_smul_add_sum_slope_smul_eq_zero.solution
