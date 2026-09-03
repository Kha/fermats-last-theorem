import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty

set_option autoImplicit false

open scoped Manifold Topology

theorem UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty {h : ℝ} (hh : 0 < h)
    {g : UpperHalfPlane → ℂ} (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) h)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hzero : UpperHalfPlane.IsZeroAtImInfty g)
    {φ : ℂ → ℂ} (hφ : ∀ τ : UpperHalfPlane, HasDerivAt φ (g τ) ↑τ) (τ : UpperHalfPlane) :
    φ (↑τ + h) = φ ↑τ := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty.solution
