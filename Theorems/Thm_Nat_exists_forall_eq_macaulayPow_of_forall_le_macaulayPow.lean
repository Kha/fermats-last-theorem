import Mathlib
import Definitions.Def_Nat_MacaulayPow
import P2M.Util
import P2M.Sol.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow

set_option autoImplicit false

theorem Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
    (H : ℕ → ℕ) (d₀ : ℕ) (hd₀ : 1 ≤ d₀)
    (hH : ∀ d, d₀ ≤ d → H (d + 1) ≤ Nat.macaulayPow d (H d)) :
    ∃ D₀ : ℕ, ∀ e, D₀ ≤ e → H (e + 1) = Nat.macaulayPow e (H e) := by p2m_exact_reverting @_root_.P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.solution
