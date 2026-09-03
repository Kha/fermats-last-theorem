import Definitions.Def_M4aLocalCFT_VocabDefs
import P2M.Util
import P2M.Sol.S_M4aLocalCFT_fieldUnitsDecomp_norm_ker_le_derive_range

set_option autoImplicit false

theorem M4aLocalCFT.fieldUnitsDecomp_norm_ker_le_derive_range
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [Finite (A.decompositionSubgroup K)]
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (M4aLocalCFT.fieldUnitsNorm (K := K) A).ker ≤
      (M4aLocalCFT.fieldUnitsDerive A g).range := by p2m_exact_reverting @_root_.P2MW.S_M4aLocalCFT_fieldUnitsDecomp_norm_ker_le_derive_range.solution
