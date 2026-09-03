import Mathlib
import P2M.Util
import P2M.Sol.S_exists_units_forall_div_sub_one_mem

set_option autoImplicit false
theorem exists_units_forall_div_sub_one_mem
    {L : Type*} [NormedField L] [CompleteSpace L]
    (M : ℕ → AddSubgroup L) (hMclosed : ∀ n, IsClosed (M n : Set L)) (hManti : Antitone M)
    (hMmul : ∀ (n : ℕ) (x y : L), x ∈ M n → y ∈ M 0 → x * y ∈ M n)
    (hMnorm : ∀ x ∈ M 0, ‖x‖ < 1)
    (hMsmall : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x ∈ M n, ‖x‖ < ε)
    (s : ℕ → Lˣ)
    (hs : ∀ n, ((s (n + 1) / s n : Lˣ) : L) - 1 ∈ M n ∧ ((s n / s (n + 1) : Lˣ) : L) - 1 ∈ M n) :
    ∃ x : Lˣ, ∀ n, ((x / s n : Lˣ) : L) - 1 ∈ M n ∧ ((s n / x : Lˣ) : L) - 1 ∈ M n := by p2m_exact_reverting @_root_.P2MW.S_exists_units_forall_div_sub_one_mem.solution
