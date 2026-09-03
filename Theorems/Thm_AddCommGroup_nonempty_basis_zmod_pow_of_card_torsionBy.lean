import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy

set_option autoImplicit false

theorem AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    {V : Type*} [AddCommGroup V] [Module (ZMod (ℓ ^ m)) V]
    (ι : V →+ M) (hι : Function.Injective ι)
    (hιr : ∀ x : M, x ∈ ι.range ↔ ((ℓ ^ m : ℕ) : ℤ) • x = 0) :
    Nonempty (Module.Basis (Fin r) (ZMod (ℓ ^ m)) V) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy.solution
