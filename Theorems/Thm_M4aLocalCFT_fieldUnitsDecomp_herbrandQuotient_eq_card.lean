import Definitions.Def_M4aLocalCFT_VocabDefs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import P2M.Util
import P2M.Sol.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card

set_option autoImplicit false
namespace M4aLocalCFT

section LocalUnitCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
variable [Finite (IsLocalRing.ResidueField A)]
variable [Finite (A.decompositionSubgroup K)] [IsCyclic (A.decompositionSubgroup K)]

variable (K) in

theorem fieldUnitsDecomp_herbrandQuotient_eq_card
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ((fieldUnitsDerive A g).ker ⧸
      ((fieldUnitsNorm (K := K) A).range.subgroupOf (fieldUnitsDerive A g).ker)) =
    Nat.card (A.decompositionSubgroup K) *
    Nat.card ((fieldUnitsNorm (K := K) A).ker ⧸
      ((fieldUnitsDerive A g).range.subgroupOf (fieldUnitsNorm (K := K) A).ker)) ∧
    Nat.card ((fieldUnitsNorm (K := K) A).ker ⧸
      ((fieldUnitsDerive A g).range.subgroupOf (fieldUnitsNorm (K := K) A).ker)) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card.solution

end LocalUnitCohomology

end M4aLocalCFT
