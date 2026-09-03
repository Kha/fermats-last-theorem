import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic

set_option autoImplicit false
open IntermediateField
theorem IntermediateField.finiteDimensional_normal_adjoin_rootsOfUnity_padic (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (N : ℕ) (hN : 0 < N) :
    FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ∧ Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic.solution
