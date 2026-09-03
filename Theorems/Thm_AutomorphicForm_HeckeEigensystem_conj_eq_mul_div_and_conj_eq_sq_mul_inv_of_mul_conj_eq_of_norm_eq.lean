import Mathlib.Analysis.Complex.Norm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_HeckeEigensystem_conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq

set_option autoImplicit false

theorem AutomorphicForm.HeckeEigensystem.conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq
    (a b : ℂ) (c : ℝ) (hc : 0 < c)
    (h1 : a * starRingEnd ℂ b = (c : ℂ) * starRingEnd ℂ a) (h2 : ‖b‖ = c) :
    starRingEnd ℂ a = (c : ℂ) * (a / b) ∧ starRingEnd ℂ b = (c : ℂ) ^ 2 * b⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_HeckeEigensystem_conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq.solution
