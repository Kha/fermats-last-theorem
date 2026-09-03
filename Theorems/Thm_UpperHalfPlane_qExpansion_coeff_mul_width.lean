import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_qExpansion_coeff_mul_width

set_option autoImplicit false

open UpperHalfPlane in
open scoped Manifold in

theorem UpperHalfPlane.qExpansion_coeff_mul_width (f : UpperHalfPlane → ℂ) (h₀ : ℝ) (hh₀ : 0 < h₀)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) h₀)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
    (m' : ℕ) (hm' : 0 < m') (i : ℕ) :
    PowerSeries.coeff i (UpperHalfPlane.qExpansion ((m' : ℝ) * h₀) f) =
      if m' ∣ i then PowerSeries.coeff (i / m') (UpperHalfPlane.qExpansion h₀ f) else 0 := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_qExpansion_coeff_mul_width.solution
