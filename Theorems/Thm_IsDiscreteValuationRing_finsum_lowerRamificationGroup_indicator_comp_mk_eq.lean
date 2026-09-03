import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq
attribute [-simp] IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf

set_option autoImplicit false
open scoped Classical in

theorem IsDiscreteValuationRing.finsum_lowerRamificationGroup_indicator_comp_mk_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (H : Subgroup G) [H.Normal] {A : Type*} [CommGroup A] (χ : G ⧸ H →* A) :
    ∑ᶠ i : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup R G (i + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup R G 0) : ℚ) *
          (if ∀ σ ∈ IsLocalRing.lowerRamificationGroup R G (i + 1), χ (QuotientGroup.mk σ) = 1 then 0 else 1) =
      ∑ᶠ j : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) 0) : ℚ) *
          (if ∀ τ ∈ IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1), χ τ = 1
            then 0 else 1) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq.solution
