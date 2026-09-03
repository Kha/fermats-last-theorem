import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_index_toAddSubgroup_maximalIdeal_pow_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.index_toAddSubgroup_maximalIdeal_pow_Rw (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] (n : ℕ) :
    (IsLocalRing.maximalIdeal (Rw q Kw) ^ n).toAddSubgroup.FiniteIndex ∧
      (IsLocalRing.maximalIdeal (Rw q Kw) ^ n).toAddSubgroup.index
        = Nat.card (IsLocalRing.ResidueField (Rw q Kw)) ^ n := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_index_toAddSubgroup_maximalIdeal_pow_Rw.solution
