import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy

set_option autoImplicit false

universe u

theorem Matrix.nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy
    (ℓ : ℕ) [Fact ℓ.Prime] (m : ℕ) [NeZero m]
    (V : Type u) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m))) V] [Finite V]
    (hV : ∀ j ≤ m, Nat.card {v : V // ℓ ^ j • v = 0} = ℓ ^ (4 * j)) :
    Nonempty (V ≃ₗ[Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m))] Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m))) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy.solution
