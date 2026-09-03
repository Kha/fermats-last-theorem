import Mathlib
import P2M.Util
import P2M.Sol.S_ZMod_exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate

set_option autoImplicit false

open scoped BigOperators

theorem ZMod.exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate
    {g d : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    (B : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) →
      (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d)
    (hadd₁ : ∀ a b c, B (a + b) c = B a c + B b c) (hadd₂ : ∀ a b c, B a (b + c) = B a b + B a c)
    (halt : ∀ a, B a a = 0) (hnd : ∀ a, (∀ b, B a b = 0) → a = 0) :
    ∃ α : (((i : Fin g) → ZMod (δ i)) × (((i : Fin g) → ZMod (δ i)) →+ ZMod d)) ≃+
        (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))),
      ∀ (h h' : (i : Fin g) → ZMod (δ i)) (c c' : ((i : Fin g) → ZMod (δ i)) →+ ZMod d),
        B (α (h, c)) (α (h', c')) = c h' - c' h := by p2m_exact_reverting @_root_.P2MW.S_ZMod_exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate.solution
