import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)]
    (hℓ : (Nat.card G).Prime) (t : ℕ)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (y : ℕ) :
    ∃ S : Finset B, S.card ≤ (if y = t then Nat.card G else 1) ∧
      (∀ s ∈ S, IsUnit s ∧ (∀ σ : G, σ • s = s) ∧ s - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y)) ∧
      ∀ a : B, IsUnit a → (∀ σ : G, σ • a = a) → a - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y) →
        ∃ s ∈ S, ∃ b : B, IsUnit b ∧
          b - 1 ∈ IsLocalRing.maximalIdeal B ^ (if y ≤ t then y else t + Nat.card G * (y - t)) ∧
          a - s * ∏ᶠ σ : G, σ • b ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (y + 1)) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card.solution
