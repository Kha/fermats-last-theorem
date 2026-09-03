import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime

set_option autoImplicit false

open Polynomial

theorem Polynomial.exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime
    (ℓ : ℕ) [Fact ℓ.Prime] (n₀ A₀ B₀ c N₀ : ℕ)
    (avoid : Polynomial (ZMod ℓ)) (havoid : avoid ≠ 0) :
    ∃ (D M : ℕ) (g : Fin M → Polynomial ℤ),
      2 ≤ D ∧ N₀ ≤ D ∧ A₀ * (c * D) ^ n₀ + B₀ < M ∧
      (∀ i, (g i).Monic ∧ (g i).natDegree = D) ∧
      (∀ i, Irreducible ((g i).map (Int.castRingHom (ZMod ℓ)))) ∧
      (∀ i, ((g i).map (Int.castRingHom (ZMod ℓ))).Separable) ∧
      (∀ i j, i ≠ j →
        IsCoprime ((g i).map (Int.castRingHom (ZMod ℓ))) ((g j).map (Int.castRingHom (ZMod ℓ)))) ∧
      (∀ i, IsCoprime ((g i).map (Int.castRingHom (ZMod ℓ))) avoid) ∧
      (∀ i, ((g i).map (Int.castRingHom (ZMod ℓ))).eval 0 ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime.solution
