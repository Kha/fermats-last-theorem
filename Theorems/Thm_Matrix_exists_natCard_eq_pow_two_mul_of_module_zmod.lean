import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_natCard_eq_pow_two_mul_of_module_zmod

set_option autoImplicit false

open scoped Quaternion

theorem Matrix.exists_natCard_eq_pow_two_mul_of_module_zmod
    (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Finite V] :
    ∃ k : ℕ, Nat.card V = ℓ ^ (2 * k) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_natCard_eq_pow_two_mul_of_module_zmod.solution
