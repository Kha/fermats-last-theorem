import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_nonempty_pi_zmod_addEquiv_torsionBy_of_card_torsionBy_eq_pow

set_option autoImplicit false

universe u

theorem AddCommGroup.nonempty_pi_zmod_addEquiv_torsionBy_of_card_torsionBy_eq_pow
    {A : Type u} [AddCommGroup A] {n : ℕ} (hn : n ≠ 0) (r : ℕ)
    (hcard : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Fin r → ZMod n) ≃+ Submodule.torsionBy ℤ A n) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_nonempty_pi_zmod_addEquiv_torsionBy_of_card_torsionBy_eq_pow.solution
