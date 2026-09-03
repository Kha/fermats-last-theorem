import Mathlib
import P2M.Util
import P2M.Sol.S_IsAlgClosed_exists_isPrimitiveRoot_pow_and_pow_succ_eq

set_option autoImplicit false

theorem IsAlgClosed.exists_isPrimitiveRoot_pow_and_pow_succ_eq
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) :
    ∃ ζ : ℕ → k, (∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) ∧ ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n := by p2m_exact_reverting @_root_.P2MW.S_IsAlgClosed_exists_isPrimitiveRoot_pow_and_pow_succ_eq.solution
