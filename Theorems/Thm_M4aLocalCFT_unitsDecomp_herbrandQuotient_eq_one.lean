import Definitions.Def_M4aLocalCFT_VocabDefs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import P2M.Util
import P2M.Sol.S_M4aLocalCFT_unitsDecomp_herbrandQuotient_eq_one

set_option autoImplicit false
namespace M4aLocalCFT

section LocalUnitCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
variable [Finite (IsLocalRing.ResidueField A)]
variable [Finite (A.decompositionSubgroup K)] [IsCyclic (A.decompositionSubgroup K)]

variable (K) in

theorem unitsDecomp_herbrandQuotient_eq_one
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ((unitsDerive A g).ker ⧸
      ((unitsNorm (K := K) A).range.subgroupOf (unitsDerive A g).ker)) =
    Nat.card ((unitsNorm (K := K) A).ker ⧸
      ((unitsDerive A g).range.subgroupOf (unitsNorm (K := K) A).ker)) ∧
    Nat.card ((unitsDerive A g).ker ⧸
      ((unitsNorm (K := K) A).range.subgroupOf (unitsDerive A g).ker)) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_M4aLocalCFT_unitsDecomp_herbrandQuotient_eq_one.solution

end LocalUnitCohomology

end M4aLocalCFT
