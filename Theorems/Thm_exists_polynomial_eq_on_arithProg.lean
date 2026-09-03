import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import P2M.Util
import P2M.Sol.S_exists_polynomial_eq_on_arithProg

open Polynomial
theorem exists_polynomial_eq_on_arithProg {n w L m₀ D : ℕ} (hD : 0 < D) (μ : ℂ) (P : Fin n → Polynomial ℂ) (hP : ∀ i, (P i).natDegree ≤ w) (x : ℕ → ℚ) (hint : ∀ m, m₀ ≤ m → ∃ z : ℤ, (D : ℚ) * x m = z) (hnear : ∀ m, m₀ ≤ m → ∃ i, ‖(x m : ℂ) - (P i).eval (μ * m)‖ < 1 / ((D : ℝ) * 2 ^ (w + 1))) : ∃ a b : ℕ, 0 < a ∧ m₀ ≤ b ∧ ∃ G : Polynomial ℚ, G.natDegree ≤ w ∧ ∀ j < L, x (b + a * j) = G.eval (j : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_exists_polynomial_eq_on_arithProg.solution
