import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_volume_setOf_mvPolynomial_eval_eq_zero

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.volume_setOf_mvPolynomial_eval_eq_zero
    {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_volume_setOf_mvPolynomial_eval_eq_zero.solution
