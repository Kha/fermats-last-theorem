import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate

set_option autoImplicit false

theorem AddMonoidHom.exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate
    {d : ℕ} [NeZero d] (K : Type) [AddCommGroup K] [Finite K]
    (B : K →+ K →+ ZMod d) (halt : ∀ a : K, B a a = 0) (hnd : ∀ a : K, (∀ b : K, B a b = 0) → a = 0) :
    ∃ (L : Type) (_ : AddCommGroup L) (_ : Fintype L) (α : L × (L →+ ZMod d) ≃+ K),
      ∀ (x x' : L) (c c' : L →+ ZMod d), B (α (x, c)) (α (x', c')) = c x' - c' x := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate.solution
