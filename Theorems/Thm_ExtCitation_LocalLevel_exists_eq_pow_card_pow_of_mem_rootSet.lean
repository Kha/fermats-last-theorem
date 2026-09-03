import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_exists_eq_pow_card_pow_of_mem_rootSet

set_option autoImplicit false
open IntermediateField ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.exists_eq_pow_card_pow_of_mem_rootSet (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (m : ℕ) (hm : ¬ q ∣ m)
    (ζ₀ : PadicAlgCl q) (hζ₀ : IsPrimitiveRoot ζ₀ m)
    (t : PadicAlgCl q) (ht : t ∈ (minpoly K ζ₀).rootSet (PadicAlgCl q)) :
    ∃ i : ℕ, t = ζ₀ ^ (Nat.card (IsLocalRing.ResidueField (Rw q K)) ^ i) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_exists_eq_pow_card_pow_of_mem_rootSet.solution
