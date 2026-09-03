import Definitions.Def_M4aLocalCFT_VocabDefs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import P2M.Util
import P2M.Sol.S_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex

set_option autoImplicit false

theorem M4aLocalCFT.unitsDecomp_exists_cohTrivial_finiteIndex
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
    [Finite (IsLocalRing.ResidueField A)]
    [Finite (A.decompositionSubgroup K)]
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ∃ V : Subgroup Aˣ, V.FiniteIndex ∧
      (∀ s : A.decompositionSubgroup K, ∀ v ∈ V, M4aLocalCFT.unitsAct A s v ∈ V) ∧
      (∀ v ∈ V, M4aLocalCFT.unitsDerive A g v = 1 →
        ∃ w ∈ V, M4aLocalCFT.unitsNorm (K := K) A w = v) ∧
      (∀ v ∈ V, M4aLocalCFT.unitsNorm (K := K) A v = 1 →
        ∃ w ∈ V, M4aLocalCFT.unitsDerive A g w = v) := by p2m_exact_reverting @_root_.P2MW.S_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex.solution
