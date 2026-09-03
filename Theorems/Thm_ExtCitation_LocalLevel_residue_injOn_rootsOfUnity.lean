import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_residue_injOn_rootsOfUnity

set_option autoImplicit false
open IntermediateField ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.residue_injOn_rootsOfUnity (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] (m : ℕ) (hm : ¬ q ∣ m)
    (ζ₁ ζ₂ : Rw q Kw) (h₁ : ζ₁ ^ m = 1) (h₂ : ζ₂ ^ m = 1)
    (h : IsLocalRing.residue (Rw q Kw) ζ₁ = IsLocalRing.residue (Rw q Kw) ζ₂) : ζ₁ = ζ₂ := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_residue_injOn_rootsOfUnity.solution
