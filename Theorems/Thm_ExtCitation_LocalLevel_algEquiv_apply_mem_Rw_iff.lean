import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_algEquiv_apply_mem_Rw_iff

set_option autoImplicit false
open ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.algEquiv_apply_mem_Rw_iff (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]
    (σ : Kw ≃ₐ[ℚ_[q]] Kw) (x : Kw) : σ x ∈ Rw q Kw ↔ x ∈ Rw q Kw := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_algEquiv_apply_mem_Rw_iff.solution
