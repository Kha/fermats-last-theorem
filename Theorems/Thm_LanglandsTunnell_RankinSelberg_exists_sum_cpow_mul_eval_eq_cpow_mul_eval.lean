import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_sum_cpow_mul_eval_eq_cpow_mul_eval

set_option autoImplicit false

theorem LanglandsTunnell.RankinSelberg.exists_sum_cpow_mul_eval_eq_cpow_mul_eval
    (N : ℕ) (hN : N ≠ 0) (ι : Type) [Fintype ι] (m : ι → ℤ) (P : ι → Polynomial ℂ) :
    ∃ (m₀ : ℤ) (P₀ : Polynomial ℂ), ∀ s : ℂ,
      ∑ i, (N : ℂ) ^ ((m i : ℂ) * s) * (P i).eval ((N : ℂ) ^ (-s)) =
        (N : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((N : ℂ) ^ (-s)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_sum_cpow_mul_eval_eq_cpow_mul_eval.solution
