import Definitions.Def_AutomorphicForm_HeckeEigensystem
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_satakePow_sq_ne_of_sq_eq_real_mul_of_norm_sq_lt

set_option autoImplicit false

theorem LanglandsTunnell.Converse.satakePow_sq_ne_of_sq_eq_real_mul_of_norm_sq_lt
    (a b : ℂ) (p : ℕ) (hp : 1 < p)
    (t : ℝ) (ht0 : 0 ≤ t) (hat : a ^ 2 = (t : ℂ) * b)
    (hab : ‖a‖ ^ 2 < ‖b‖ * ((p : ℝ) + 2 + (p : ℝ)⁻¹))
    (f : ℕ) (hf : 0 < f) :
    AutomorphicForm.satakePow f a b ^ 2 ≠
      b ^ f * (((p ^ f : ℕ) : ℂ) + 2 + ((p ^ f : ℕ) : ℂ)⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_satakePow_sq_ne_of_sq_eq_real_mul_of_norm_sq_lt.solution
