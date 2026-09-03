import Definitions.Def_M4aLocalCFT_VocabDefs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import P2M.Util
import P2M.Sol.S_M4aLocalCFT_unitsDecomp_cohTrivial_of_inertia_eq_bot

set_option autoImplicit false
namespace M4aLocalCFT

section LocalUnitCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
variable [Finite (IsLocalRing.ResidueField A)]
variable [Finite (A.decompositionSubgroup K)] [IsCyclic (A.decompositionSubgroup K)]

variable (K) in

theorem unitsDecomp_cohTrivial_of_inertia_eq_bot
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hur : A.inertiaSubgroup K = ⊥) :
    (unitsDerive A g).ker ≤ (unitsNorm (K := K) A).range ∧
    (unitsNorm (K := K) A).ker ≤ (unitsDerive A g).range := by p2m_exact_reverting @_root_.P2MW.S_M4aLocalCFT_unitsDecomp_cohTrivial_of_inertia_eq_bot.solution

end LocalUnitCohomology

end M4aLocalCFT
