import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.Analysis.Complex.Basic
import P2M.Util
import P2M.Sol.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball
open scoped ComplexOrder
open Complex Set Metric LSeries
namespace LSeries
theorem abscissaOfAbsConv_lt_of_differentiableOn_ball {a : ℕ → ℂ} (ha : 0 ≤ a) {x : ℝ}
    (hx : abscissaOfAbsConv a ≤ x) {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball (x:ℂ) r))
    (hfa : ∀ s ∈ ball (x:ℂ) r, x < s.re → f s = LSeries a s) :
    abscissaOfAbsConv a < x := by p2m_exact_reverting @_root_.P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.solution
end LSeries
