import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Bases
import P2M.Util
import P2M.Sol.S_Complex_countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero

theorem Complex.countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero
    (f : ℂ → ℂ) (σ : ℝ)
    (hf : DifferentiableOn ℂ f {s : ℂ | σ < s.re})
    (hne : ∃ s : ℂ, σ < s.re ∧ f s ≠ 0) :
    Set.Countable {s : ℂ | σ < s.re ∧ f s = 0} := by p2m_exact_reverting @_root_.P2MW.S_Complex_countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero.solution
