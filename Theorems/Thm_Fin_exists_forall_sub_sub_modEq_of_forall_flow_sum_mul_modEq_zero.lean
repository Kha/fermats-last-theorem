import Mathlib
import P2M.Util
import P2M.Sol.S_Fin_exists_forall_sub_sub_modEq_of_forall_flow_sum_mul_modEq_zero

set_option autoImplicit false

theorem Fin.exists_forall_sub_sub_modEq_of_forall_flow_sum_mul_modEq_zero
    (n m : ℕ) (src tgt : Fin m → Fin n) (q : ℤ) (τ : Fin m → ℤ)
    (hτ : ∀ ε : Fin m → ℤ,
      (∀ i : Fin n, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0)) →
      (∑ e, ε e * τ e) ≡ 0 [ZMOD q]) :
    ∃ φ : Fin n → ℤ, ∀ e : Fin m, τ e ≡ φ (tgt e) - φ (src e) [ZMOD q] := by p2m_exact_reverting @_root_.P2MW.S_Fin_exists_forall_sub_sub_modEq_of_forall_flow_sum_mul_modEq_zero.solution
