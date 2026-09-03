import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.exists_relative_ramification_inertia_Rw (q : ℕ) [Fact q.Prime]
    (Kw Lw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]
    [FiniteDimensional ℚ_[q] Lw] (hKL : Kw ≤ Lw) :
    ∃ (e f : ℕ) (ι : Rw q Kw →+* Rw q Lw),
      (∀ x : Rw q Kw, (((ι x : Rw q Lw) : Lw) : PadicAlgCl q) = ((x : Kw) : PadicAlgCl q)) ∧
      0 < e ∧ 0 < f ∧
      Ideal.map ι (IsLocalRing.maximalIdeal (Rw q Kw)) = IsLocalRing.maximalIdeal (Rw q Lw) ^ e ∧
      Nat.card (IsLocalRing.ResidueField (Rw q Lw)) = Nat.card (IsLocalRing.ResidueField (Rw q Kw)) ^ f ∧
      Module.finrank ℚ_[q] Lw = Module.finrank ℚ_[q] Kw * (e * f) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw.solution
