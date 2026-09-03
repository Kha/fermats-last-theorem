import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)]
    (h0 : IsLocalRing.lowerRamificationGroup B G 0 = ⊥) (m : ℕ)
    (a : B) (ha : IsUnit a) (hfix : ∀ σ : G, σ • a = a) (ham : a - 1 ∈ IsLocalRing.maximalIdeal B ^ m) :
    ∃ b : B, IsUnit b ∧ b - 1 ∈ IsLocalRing.maximalIdeal B ^ m ∧
      a - ∏ᶠ σ : G, σ • b ∈ IsLocalRing.maximalIdeal B ^ (m + 1) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot.solution
