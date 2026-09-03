import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_finsum_card_lowerRamificationGroup_mul_apply_map_mk_eq_of_apply_bot_eq_zero
attribute [-simp] IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf

set_option autoImplicit false

theorem IsDiscreteValuationRing.finsum_card_lowerRamificationGroup_mul_apply_map_mk_eq_of_apply_bot_eq_zero
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (H : Subgroup G) [H.Normal] (f : Subgroup (G ⧸ H) → ℚ) (hf : f ⊥ = 0) :
    (IsLocalRing.lowerRamificationGroup R G 0).map (QuotientGroup.mk' H) =
        IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) 0 ∧
    ∑ᶠ i : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup R G (i + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup R G 0) : ℚ) *
          f ((IsLocalRing.lowerRamificationGroup R G (i + 1)).map (QuotientGroup.mk' H)) =
      ∑ᶠ j : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) 0) : ℚ) *
          f (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1)) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_finsum_card_lowerRamificationGroup_mul_apply_map_mk_eq_of_apply_bot_eq_zero.solution
