import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_exists_pow_smul_mem_span_of_linearIndependent_of_mem_Rw

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.exists_pow_smul_mem_span_of_linearIndependent_of_mem_Rw
    (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]
    {ι : Type*} [Fintype ι] (w : ι → Kw) (hw : LinearIndependent ℚ_[q] w)
    (hcard : Fintype.card ι = Module.finrank ℚ_[q] Kw) :
    ∃ N : ℕ, ∀ x : Kw, x ∈ Rw q Kw →
      ((q : ℚ_[q]) ^ N) • x ∈ Submodule.span ℤ_[q] (Set.range w) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_exists_pow_smul_mem_span_of_linearIndependent_of_mem_Rw.solution
