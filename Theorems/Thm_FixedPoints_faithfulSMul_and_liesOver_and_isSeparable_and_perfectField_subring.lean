import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild
import P2M.Util
import P2M.Sol.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring

set_option autoImplicit false

theorem FixedPoints.faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)]
    (H : Subgroup G) [H.Normal] :
    FaithfulSMul (G ⧸ H) (FixedPoints.subring R H) ∧
    PerfectField (IsLocalRing.ResidueField (FixedPoints.subring R H)) ∧
    ∃ (_ : (IsLocalRing.maximalIdeal (FixedPoints.subring R H)).LiesOver
      (IsLocalRing.maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)))),
      Algebra.IsSeparable
        (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H) ⧸
          IsLocalRing.maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)))
        (FixedPoints.subring R H ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R H)) := by p2m_exact_reverting @_root_.P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.solution
