import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul

set_option autoImplicit false

theorem AddMonoidHom.sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul
    {V : Type*} [AddCommGroup V] (m : V →+ V) (t : ℤ) (hm : ∀ T, m (m T) - t • m T + T = 0)
    (P : V) (c : ℤ) (hP : m P = c • P) :
    (c ^ 2 - t * c + 1) • P = 0 := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul.solution
