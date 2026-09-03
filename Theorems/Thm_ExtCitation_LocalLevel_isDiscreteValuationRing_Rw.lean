import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.isDiscreteValuationRing_Rw (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] :
    IsDiscreteValuationRing (Rw q Kw) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw.solution
