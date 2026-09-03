import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_exists_isRegular_pair_of_two_le_ringKrullDim

set_option autoImplicit false

theorem IsIntegrallyClosed.exists_isRegular_pair_of_two_le_ringKrullDim
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B] [IsIntegrallyClosed B]
    (hdim : 2 ≤ ringKrullDim B) (t : B) (ht : t ∈ IsLocalRing.maximalIdeal B) (ht0 : t ≠ 0) :
    ∃ b : B, b ∈ IsLocalRing.maximalIdeal B ∧ RingTheory.Sequence.IsRegular B [t, b] := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_exists_isRegular_pair_of_two_le_ringKrullDim.solution
