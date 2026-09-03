import Mathlib
import P2M.Util
import P2M.Sol.S_Real_tsum_comp_add_intCast_eq_tsum_integral_mul_cexp

set_option autoImplicit false

open MeasureTheory TopologicalSpace

theorem Real.tsum_comp_add_intCast_eq_tsum_integral_mul_cexp
    {d : Type*} [Fintype d] (f : C(d → ℝ, ℂ))
    (h_norm : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict K‖)
    (h_sum : Summable fun n : d → ℤ =>
      ∫ y : d → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * y i : ℝ) : ℂ))) * f y)
    (x : d → ℝ) :
    ∑' n : d → ℤ, f (x + fun i => (n i : ℝ)) =
      ∑' n : d → ℤ, (∫ y : d → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * y i : ℝ) : ℂ))) * f y) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * x i : ℝ) : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_Real_tsum_comp_add_intCast_eq_tsum_integral_mul_cexp.solution
