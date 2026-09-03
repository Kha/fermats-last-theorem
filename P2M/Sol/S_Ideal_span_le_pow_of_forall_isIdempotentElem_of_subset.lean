import Mathlib
import P2M.Util
namespace P2MW.S_Ideal_span_le_pow_of_forall_isIdempotentElem_of_subset

set_option autoImplicit false
universe u

theorem solution
    {R : Type u} [CommRing R] (S : Set R) (hS : ∀ e ∈ S, IsIdempotentElem e)
    (𝔭 : Ideal R) (hS𝔭 : S ⊆ 𝔭) (n : ℕ) : Ideal.span S ≤ 𝔭 ^ n := by
  rcases n with _ | n
  · rw [pow_zero, Ideal.one_eq_top]; exact le_top
  · rw [Ideal.span_le]
    intro e he
    have h := Ideal.pow_mem_pow (hS𝔭 he) (n + 1)
    rwa [(hS e he).pow_succ_eq] at h
