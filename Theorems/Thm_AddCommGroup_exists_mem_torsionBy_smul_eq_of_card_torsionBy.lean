import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy

set_option autoImplicit false

theorem AddCommGroup.exists_mem_torsionBy_smul_eq_of_card_torsionBy (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m + 1, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    (x : M) (hx : x ∈ Submodule.torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ)) :
    ∃ y ∈ Submodule.torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ), ℓ • y = x := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy.solution
