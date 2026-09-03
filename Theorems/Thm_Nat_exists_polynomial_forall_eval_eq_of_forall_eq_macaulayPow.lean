import Mathlib
import Definitions.Def_Nat_MacaulayPow
import P2M.Util
import P2M.Sol.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow

set_option autoImplicit false

theorem Nat.exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow
    (H : ℕ → ℕ) (D₀ : ℕ) (hD₀ : 1 ≤ D₀)
    (hH : ∀ e, D₀ ≤ e → H (e + 1) = Nat.macaulayPow e (H e)) :
    ∃ P : Polynomial ℚ, ∀ e, D₀ ≤ e → (H e : ℚ) = P.eval (e : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow.solution
