import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_AutomorphicForm_summable_integral_rpow_neg_and_summable_rpow_neg_of_ncard_spread_le

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.summable_integral_rpow_neg_and_summable_rpow_neg_of_ncard_spread_le
    (V : Type) [Fintype V] [Nonempty V] (ιE : Type) (nE : ιE → ℕ)
    (τ τ' : ιE → V → ℝ) (C : ℝ) (d : ℕ)
    (hcount : ∀ R : ℝ, 0 ≤ R →
      {e : ιE | 0 < nE e ∧ ∑ v : V, ∑ v' : V, |τ e v - τ e v'| ≤ R}.Finite ∧
      (({e : ιE | 0 < nE e ∧ ∑ v : V, ∑ v' : V, |τ e v - τ e v'| ≤ R}.ncard : ℕ) : ℝ) ≤ C * (1 + R) ^ d) :
    ∀ B : ℕ, d + 3 ≤ B →
      Summable (fun e : ιE => if 0 < nE e then
        ∫ t : ℝ, (1 + ∑ v : V, (|t + τ e v| + |t - τ' e v|)) ^ (-(B : ℝ)) else 0) ∧
      Summable (fun e : ιE => if 0 < nE e then
        (1 + ∑ v : V, (|τ e v| + |τ' e v|)) ^ (-(B : ℝ)) else 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_summable_integral_rpow_neg_and_summable_rpow_neg_of_ncard_spread_le.solution
