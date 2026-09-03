import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral

set_option autoImplicit false
open ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.mem_Rw_iff_isIntegral (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] (x : Kw) :
    x ∈ Rw q Kw ↔ IsIntegral ℤ_[q] (x : PadicAlgCl q) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral.solution
