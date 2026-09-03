import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integrable_one_add_sum_abs_add_abs_sub_rpow_neg

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.integrable_one_add_sum_abs_add_abs_sub_rpow_neg
    (V : Type) [Fintype V] [Nonempty V] (τ τ' : V → ℝ) (B : ℝ) (hB : 2 ≤ B) :
    MeasureTheory.Integrable
      (fun t : ℝ => (1 + ∑ v : V, (|t + τ v| + |t - τ' v|)) ^ (-B)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integrable_one_add_sum_abs_add_abs_sub_rpow_neg.solution
