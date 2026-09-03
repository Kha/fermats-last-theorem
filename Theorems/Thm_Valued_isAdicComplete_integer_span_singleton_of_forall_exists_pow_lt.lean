import Mathlib
import P2M.Util
import P2M.Sol.S_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt

set_option autoImplicit false
open Valued Filter Topology in

theorem Valued.isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [hK : Valued K Γ₀]
    [CompleteSpace K] (ϖ : 𝒪[K]) (hϖ0 : (ϖ : K) ≠ 0)
    (harch : ∀ γ : Γ₀, γ ≠ 0 → ∃ n : ℕ, Valued.v (ϖ : K) ^ n < γ) :
    IsAdicComplete (Ideal.span {ϖ}) 𝒪[K] := by p2m_exact_reverting @_root_.P2MW.S_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt.solution
