import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_index_principalUnits_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel IsLocalRing
theorem ExtCitation.LocalLevel.index_principalUnits_Rw (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] {k : ℕ} (hk : 1 ≤ k) :
    (principalUnits (Rw q Kw) k).FiniteIndex ∧
      (principalUnits (Rw q Kw) k).index
        = (Nat.card (IsLocalRing.ResidueField (Rw q Kw)) - 1) * Nat.card (IsLocalRing.ResidueField (Rw q Kw)) ^ (k - 1) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_index_principalUnits_Rw.solution
