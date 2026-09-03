import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy

set_option autoImplicit false

theorem AddCommGroup.exists_basis_smul_eq_of_card_torsionBy (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m + 1, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    {V : Type*} [AddCommGroup V] [Module (ZMod (ℓ ^ m)) V]
    (ι : V →+ M) (hι : Function.Injective ι)
    (hιr : ∀ x : M, x ∈ ι.range ↔ ((ℓ ^ m : ℕ) : ℤ) • x = 0)
    {V' : Type*} [AddCommGroup V'] [Module (ZMod (ℓ ^ (m + 1))) V']
    (ι' : V' →+ M) (hι' : Function.Injective ι')
    (hι'r : ∀ x : M, x ∈ ι'.range ↔ ((ℓ ^ (m + 1) : ℕ) : ℤ) • x = 0)
    (c : Module.Basis (Fin r) (ZMod (ℓ ^ m)) V) :
    ∃ c' : Module.Basis (Fin r) (ZMod (ℓ ^ (m + 1))) V', ∀ i, ι (c i) = ℓ • ι' (c' i) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy.solution
