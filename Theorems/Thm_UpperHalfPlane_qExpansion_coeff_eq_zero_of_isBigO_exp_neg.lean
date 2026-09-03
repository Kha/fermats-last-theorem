import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg

set_option autoImplicit false

open UpperHalfPlane in
open scoped Manifold in

theorem UpperHalfPlane.qExpansion_coeff_eq_zero_of_isBigO_exp_neg (f : UpperHalfPlane → ℂ)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
    (L : ℝ) (hO : f =O[UpperHalfPlane.atImInfty] fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * L) * τ.im))
    (n : ℕ) (hn : (n : ℝ) < L) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f) = 0 := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg.solution
