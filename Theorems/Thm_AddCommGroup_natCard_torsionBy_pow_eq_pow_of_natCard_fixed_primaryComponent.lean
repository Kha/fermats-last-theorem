import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent

set_option autoImplicit false

theorem AddCommGroup.natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent
    {A : Type*} [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (τ : A →+ A)
    (hfin : Finite (Submodule.torsionBy ℤ A (ℓ : ℤ)))
    (hle : Nat.card (Submodule.torsionBy ℤ A (ℓ : ℤ)) ≤ ℓ ^ r)
    (hτ : ∀ x : A, ℓ ^ 2 • x = 0 → τ x = x)
    (hfix : ∃ c k₀ : ℕ, ∀ k : ℕ,
      Nat.card {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ (k₀ + k)] x = x} =
        ℓ ^ (r * k + c))
    (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ A ((ℓ ^ n : ℕ) : ℤ)) = ℓ ^ (r * n) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent.solution
