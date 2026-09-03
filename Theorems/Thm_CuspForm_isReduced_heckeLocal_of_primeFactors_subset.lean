import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
import P2M.Sol.S_CuspForm_isReduced_heckeLocal_of_primeFactors_subset

theorem CuspForm.isReduced_heckeLocal_of_primeFactors_subset (N : ℕ) [NeZero N] (S : Set ℕ)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪) :
    IsReduced (CuspForm.heckeLocal N S 𝒪 θ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_isReduced_heckeLocal_of_primeFactors_subset.solution
