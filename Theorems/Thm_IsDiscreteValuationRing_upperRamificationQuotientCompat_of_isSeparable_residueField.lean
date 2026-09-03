import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_upperRamificationQuotientCompat_of_isSeparable_residueField
attribute [-simp] IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf

set_option autoImplicit false

theorem IsDiscreteValuationRing.upperRamificationQuotientCompat_of_isSeparable_residueField
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (H : Subgroup G) [H.Normal] :
    IsLocalRing.UpperRamificationQuotientCompat R G (FixedPoints.subring R H) H := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_upperRamificationQuotientCompat_of_isSeparable_residueField.solution
