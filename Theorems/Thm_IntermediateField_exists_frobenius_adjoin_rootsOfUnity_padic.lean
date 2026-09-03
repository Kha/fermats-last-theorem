import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_frobenius_adjoin_rootsOfUnity_padic

set_option autoImplicit false
open IntermediateField ExtCitation.LocalLevel
theorem IntermediateField.exists_frobenius_adjoin_rootsOfUnity_padic (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (N : ℕ) (hN : 0 < N) :
    ∃ (φ : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K]
           (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (a : ℕ), 0 < a ∧
      Nat.card (IsLocalRing.ResidueField (Rw q K)) = q ^ a ∧
      ∀ ζ : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}),
        (ζ : PadicAlgCl q) ^ (q ^ N - 1) = 1 → (φ ζ : PadicAlgCl q) = (ζ : PadicAlgCl q) ^ (q ^ a) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_frobenius_adjoin_rootsOfUnity_padic.solution
