import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_finiteIndex_toAddSubgroup_span_pow_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.finiteIndex_toAddSubgroup_span_pow_Rw (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] (N : ℕ) :
    (Ideal.span {((q : ℕ) : Rw q Kw) ^ N}).toAddSubgroup.FiniteIndex := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_finiteIndex_toAddSubgroup_span_pow_Rw.solution
