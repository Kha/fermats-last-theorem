import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero

set_option autoImplicit false

universe u

theorem AddCommGroup.nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero
    (L : Type u) [AddCommGroup L] [Finite L] (d : ℕ) [NeZero d] (hd : ∀ x : L, d • x = 0) :
    Nonempty ((L →+ ZMod d) ≃+ L) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero.solution
