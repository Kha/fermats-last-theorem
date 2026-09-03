import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_DifferentFiltrationFormula
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_differentEqPowFiltrationSum_fixedPoints_subring

set_option autoImplicit false

theorem IsDiscreteValuationRing.differentEqPowFiltrationSum_fixedPoints_subring
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)] :
    DifferentEqPowFiltrationSum (FixedPoints.subring B G) B G := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_differentEqPowFiltrationSum_fixedPoints_subring.solution
