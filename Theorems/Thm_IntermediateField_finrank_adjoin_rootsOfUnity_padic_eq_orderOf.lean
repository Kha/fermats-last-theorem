import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf

set_option autoImplicit false
open IntermediateField ExtCitation.LocalLevel
theorem IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (N : ℕ) (hN : 0 < N) :
    Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})
      = orderOf ((Nat.card (IsLocalRing.ResidueField (Rw q K)) : ZMod (q ^ N - 1))) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf.solution
