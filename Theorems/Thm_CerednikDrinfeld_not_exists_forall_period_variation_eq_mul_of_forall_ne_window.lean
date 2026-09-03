import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_not_exists_forall_period_variation_eq_mul_of_forall_ne_window

set_option autoImplicit false

theorem CerednikDrinfeld.not_exists_forall_period_variation_eq_mul_of_forall_ne_window
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p]
    {G : Type} [AddCommGroup G] (x₀ : G →+ κ)
    (a₁ a₁₀ a₁₁ a₂₀ s t r : κ) (ha₁ : a₁ ≠ 0)
    (hper : ∀ g : G, a₁ ^ p * x₀ g =
      (a₁ ^ p * a₁₀ + a₁ * a₁₁) * x₀ g ^ p + (a₁ ^ (p + 1) * a₂₀ - a₁ * a₁₀ ^ p * a₁₁) * x₀ g ^ (p ^ 2))
    (g₁ g₂ : G) (hind : ∀ c₁ c₂ : ℤ, c₁ • x₀ g₁ + c₂ • x₀ g₂ = 0 → (p : ℤ) ∣ c₁ ∧ (p : ℤ) ∣ c₂)
    (hwin : ∀ c₁ c₂ : κ,
      ¬ (s = c₁ * a₁ - c₂ * a₁₀ ∧ t = -(c₁ * a₁ ^ p) - c₂ * a₁₁ ∧ r = -(c₁ * a₁₀ ^ p) - c₂ * a₂₀)) :
    ¬ ∃ μ : κ, ∀ g : G,
      (a₁ ^ (p + 1) * r - a₁ * a₁₀ ^ p * t) * x₀ g ^ (p ^ 2) + (a₁ ^ p * s + a₁ * t) * x₀ g ^ p = μ * x₀ g := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_not_exists_forall_period_variation_eq_mul_of_forall_ne_window.solution
