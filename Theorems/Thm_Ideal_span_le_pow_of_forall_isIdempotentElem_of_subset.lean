import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_span_le_pow_of_forall_isIdempotentElem_of_subset

set_option autoImplicit false
universe u

theorem Ideal.span_le_pow_of_forall_isIdempotentElem_of_subset
    {R : Type u} [CommRing R] (S : Set R) (hS : ∀ e ∈ S, IsIdempotentElem e)
    (𝔭 : Ideal R) (hS𝔭 : S ⊆ 𝔭) (n : ℕ) : Ideal.span S ≤ 𝔭 ^ n := by p2m_exact_reverting @_root_.P2MW.S_Ideal_span_le_pow_of_forall_isIdempotentElem_of_subset.solution
