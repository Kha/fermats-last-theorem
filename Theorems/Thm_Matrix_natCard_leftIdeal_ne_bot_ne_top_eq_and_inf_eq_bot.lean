import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot

set_option autoImplicit false

open scoped Quaternion

theorem Matrix.natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Nat.card {I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) // I ≠ ⊥ ∧ I ≠ ⊤} = ℓ + 1 ∧
    ∀ I I' : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)),
      I ≠ ⊥ → I ≠ ⊤ → I' ≠ ⊥ → I' ≠ ⊤ → I ≠ I' → I ⊓ I' = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot.solution
