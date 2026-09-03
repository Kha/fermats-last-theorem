import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_adjoin_rootsOfUnity_padic_mono

set_option autoImplicit false
open IntermediateField
theorem IntermediateField.adjoin_rootsOfUnity_padic_mono (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) {N N' : ℕ} (h : N ∣ N') :
    IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} ≤
      IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1} := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_adjoin_rootsOfUnity_padic_mono.solution
