import Mathlib
import P2M.Util
import P2M.Sol.S_exists_idempotent_tower_of_finite_quotient_of_isMaximal

theorem exists_idempotent_tower_of_finite_quotient_of_isMaximal
    {L : Type} [CommRing L] (ℓ : L) (hfin : Finite (L ⧸ Ideal.span {ℓ}))
    (𝔓 : Ideal L) [𝔓.IsMaximal] (hℓ : ℓ ∈ 𝔓)
    {T : Type} [CommRing T] (π : T →+* L)
    (hdense : ∀ (m : ℕ) (x : L), ∃ y : T, π y - x ∈ Ideal.span {ℓ ^ m}) :
    ∃ e : ℕ → T,
      (∀ m : ℕ, π (e m) * π (e m) - π (e m) ∈ Ideal.span {ℓ ^ m}) ∧
      (∀ m : ℕ, π (e (m + 1)) - π (e m) ∈ Ideal.span {ℓ ^ m}) ∧
      (∀ m : ℕ, 1 - π (e m) ∈ 𝔓) ∧
      (∀ (m : ℕ) (𝔪 : Ideal L), 𝔪.IsMaximal → ℓ ∈ 𝔪 → 𝔪 ≠ 𝔓 → π (e m) ∈ 𝔪) ∧
      (∀ m : ℕ, ∃ N : ℕ, ∀ x ∈ 𝔓 ^ N, π (e m) * x ∈ Ideal.span {ℓ ^ m}) := by p2m_exact_reverting @_root_.P2MW.S_exists_idempotent_tower_of_finite_quotient_of_isMaximal.solution
