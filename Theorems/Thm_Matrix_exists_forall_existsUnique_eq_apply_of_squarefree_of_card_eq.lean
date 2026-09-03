import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_forall_existsUnique_eq_apply_of_squarefree_of_card_eq

set_option autoImplicit false

theorem Matrix.exists_forall_existsUnique_eq_apply_of_squarefree_of_card_eq
    (N : ℕ) [NeZero N] (hN : Squarefree N) (V : Type) [AddCommGroup V] [Module (ZMod N) V] [Finite V]
    (hV : Nat.card V = N ^ 4) (α : Matrix (Fin 2) (Fin 2) (ZMod N) →+* Module.End (ZMod N) V) :
    ∃ v₀ : V, ∀ w : V, ∃! a : Matrix (Fin 2) (Fin 2) (ZMod N), w = α a v₀ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_forall_existsUnique_eq_apply_of_squarefree_of_card_eq.solution
