import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    (hℓ : (Nat.card G).Prime)
    (t : ℕ) (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤)
    (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (n : ℕ) (hn : t < n) (a : FixedPoints.subring B G)
    (ha : (a : B) - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * n)) :
    ∃ b : B, b - 1 ∈ IsLocalRing.maximalIdeal B ^ (t + Nat.card G * (n - t)) ∧
      (∏ᶠ σ : G, σ • b) - a ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (n + 1)) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card.solution
