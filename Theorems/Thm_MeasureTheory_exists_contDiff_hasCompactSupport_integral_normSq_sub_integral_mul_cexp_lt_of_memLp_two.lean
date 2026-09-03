import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_contDiff_hasCompactSupport_integral_normSq_sub_integral_mul_cexp_lt_of_memLp_two

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate ContDiff

theorem MeasureTheory.exists_contDiff_hasCompactSupport_integral_normSq_sub_integral_mul_cexp_lt_of_memLp_two
    (G : ℝ → ℂ) (_hG : MemLp G 2) (ε : ℝ) (_hε : 0 < ε) :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      MemLp (fun t : ℝ => ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) 2 ∧
      ∫ t : ℝ, ‖G t - ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ ^ 2 < ε := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_contDiff_hasCompactSupport_integral_normSq_sub_integral_mul_cexp_lt_of_memLp_two.solution
