import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_isAdicComplete_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.isAdicComplete_Rw (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] :
    IsAdicComplete (IsLocalRing.maximalIdeal (Rw q Kw)) (Rw q Kw) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_isAdicComplete_Rw.solution
