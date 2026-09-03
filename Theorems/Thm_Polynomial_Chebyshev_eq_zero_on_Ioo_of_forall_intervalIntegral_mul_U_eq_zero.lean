import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import P2M.Util
import P2M.Sol.S_Polynomial_Chebyshev_eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero

set_option autoImplicit false

open Polynomial

theorem Polynomial.Chebyshev.eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero
    (g : ℝ → ℂ) (hg : ContinuousOn g (Set.Ioo 0 Real.pi))
    (hgi : IntervalIntegrable g MeasureTheory.volume 0 Real.pi)
    (hmodes : ∀ j : ℕ,
      ∫ θ in (0 : ℝ)..Real.pi, g θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) = 0) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, g θ = 0 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_Chebyshev_eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero.solution
