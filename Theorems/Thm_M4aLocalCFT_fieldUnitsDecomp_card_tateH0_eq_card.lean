import Definitions.Def_M4aLocalCFT_VocabDefs
import P2M.Util
import P2M.Sol.S_M4aLocalCFT_fieldUnitsDecomp_card_tateH0_eq_card

set_option autoImplicit false

theorem M4aLocalCFT.fieldUnitsDecomp_card_tateH0_eq_card
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
    [Finite (IsLocalRing.ResidueField A)]
    [Finite (A.decompositionSubgroup K)]
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ((M4aLocalCFT.fieldUnitsDerive A g).ker ⧸
      ((M4aLocalCFT.fieldUnitsNorm (K := K) A).range.subgroupOf (M4aLocalCFT.fieldUnitsDerive A g).ker)) =
    Nat.card (A.decompositionSubgroup K) := by p2m_exact_reverting @_root_.P2MW.S_M4aLocalCFT_fieldUnitsDecomp_card_tateH0_eq_card.solution
