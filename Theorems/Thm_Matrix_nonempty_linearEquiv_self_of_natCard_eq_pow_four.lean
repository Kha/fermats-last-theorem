import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_four

set_option autoImplicit false

open scoped Quaternion

theorem Matrix.nonempty_linearEquiv_self_of_natCard_eq_pow_four
    (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Finite V]
    (hV : Nat.card V = ℓ ^ 4) :
    Nonempty (V ≃ₗ[Matrix (Fin 2) (Fin 2) (ZMod ℓ)] Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_four.solution
