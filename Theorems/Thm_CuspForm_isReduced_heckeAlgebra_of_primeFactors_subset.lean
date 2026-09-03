import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset

theorem CuspForm.isReduced_heckeAlgebra_of_primeFactors_subset (N : ℕ) [NeZero N] (S : Set ℕ)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) :
    IsReduced (CuspForm.heckeAlgebra N 2 S) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset.solution
