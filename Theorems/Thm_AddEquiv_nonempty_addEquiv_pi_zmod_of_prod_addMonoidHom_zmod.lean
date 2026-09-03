import Mathlib
import P2M.Util
import P2M.Sol.S_AddEquiv_nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod

set_option autoImplicit false

open scoped BigOperators

theorem AddEquiv.nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod
    {g d : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    (L : Type) [AddCommGroup L] [Finite L]
    (e : L × (L →+ ZMod d) ≃+ (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) :
    Nonempty (L ≃+ ((i : Fin g) → ZMod (δ i))) := by p2m_exact_reverting @_root_.P2MW.S_AddEquiv_nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod.solution
