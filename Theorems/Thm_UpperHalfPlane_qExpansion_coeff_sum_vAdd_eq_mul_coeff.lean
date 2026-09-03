import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff

set_option autoImplicit false

open UpperHalfPlane in
open scoped Manifold in

theorem UpperHalfPlane.qExpansion_coeff_sum_vAdd_eq_mul_coeff (f : UpperHalfPlane → ℂ) (h₀ : ℕ) (hh₀ : 0 < h₀)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (h₀ : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) (m : ℕ) :
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1
        (fun τ : UpperHalfPlane => ∑ j ∈ Finset.range h₀, f (((j : ℕ) : ℝ) +ᵥ τ))) =
      (h₀ : ℂ) * PowerSeries.coeff (h₀ * m) (UpperHalfPlane.qExpansion (h₀ : ℝ) f) := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff.solution
