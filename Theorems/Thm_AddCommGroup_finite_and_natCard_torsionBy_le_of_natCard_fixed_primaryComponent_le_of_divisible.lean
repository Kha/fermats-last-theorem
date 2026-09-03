import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible

set_option autoImplicit false

theorem AddCommGroup.finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible
    {A : Type*} [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (τ : A →+ A)
    (hexh : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ k : ℕ, (⇑τ)^[ℓ ^ k] x = x)
    (hfix : ∃ c : ℕ, ∀ k : ℕ,
      Finite {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x} ∧
      Nat.card {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k] x = x} ≤
        ℓ ^ (r * k + c))
    (hdiv : ∀ x ∈ AddCommGroup.primaryComponent A ℓ, ∃ y : A, ℓ • y = x) :
    Finite (Submodule.torsionBy ℤ A (ℓ : ℤ)) ∧
      Nat.card (Submodule.torsionBy ℤ A (ℓ : ℤ)) ≤ ℓ ^ r := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible.solution
