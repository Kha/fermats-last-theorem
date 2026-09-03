import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_exists_ramification_inertia_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.exists_ramification_inertia_Rw (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] :
    ∃ e f : ℕ, 0 < e ∧ 0 < f ∧
      Ideal.span {((q : ℕ) : Rw q Kw)} = IsLocalRing.maximalIdeal (Rw q Kw) ^ e ∧
      Nat.card (IsLocalRing.ResidueField (Rw q Kw)) = q ^ f ∧
      e * f = Module.finrank ℚ_[q] Kw := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_exists_ramification_inertia_Rw.solution
