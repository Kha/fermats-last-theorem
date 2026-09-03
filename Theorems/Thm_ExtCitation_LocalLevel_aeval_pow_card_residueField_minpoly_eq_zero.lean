import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_aeval_pow_card_residueField_minpoly_eq_zero

set_option autoImplicit false
open IntermediateField ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.aeval_pow_card_residueField_minpoly_eq_zero (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (m : ℕ) (hm : ¬ q ∣ m)
    (ζ₀ : PadicAlgCl q) (hζ₀ : IsPrimitiveRoot ζ₀ m) :
    ∃ a : ℕ, 0 < a ∧ Nat.card (IsLocalRing.ResidueField (Rw q K)) = q ^ a ∧
      Polynomial.aeval (ζ₀ ^ (q ^ a)) (minpoly K ζ₀) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_aeval_pow_card_residueField_minpoly_eq_zero.solution
