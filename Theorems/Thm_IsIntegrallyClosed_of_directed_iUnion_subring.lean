import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_of_directed_iUnion_subring

universe u v

theorem IsIntegrallyClosed.of_directed_iUnion_subring
    {B : Type u} [CommRing B] [IsDomain B] {ι : Type v} [Nonempty ι] (S : ι → Subring B)
    (hdir : Directed (· ≤ ·) S) (hcov : ∀ x : B, ∃ i, x ∈ S i)
    (hS : ∀ i, IsIntegrallyClosed (S i)) :
    IsIntegrallyClosed B := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_of_directed_iUnion_subring.solution
