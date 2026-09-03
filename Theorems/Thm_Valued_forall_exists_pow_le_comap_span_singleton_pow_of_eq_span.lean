import Mathlib
import P2M.Util
import P2M.Sol.S_Valued_forall_exists_pow_le_comap_span_singleton_pow_of_eq_span

set_option autoImplicit false
open Valued in

theorem Valued.forall_exists_pow_le_comap_span_singleton_pow_of_eq_span
    {B : Type*} [CommRing B] {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [hK : Valued K Γ₀]
    (𝔪 : Ideal B) (ev : B →+* 𝒪[K]) (G : Set B) (hG : 𝔪 = Ideal.span G)
    (δ : Γ₀) (hδ : ∀ g ∈ G, Valued.v (ev g : K) ≤ δ) (ϖ : 𝒪[K]) (hϖ0 : (ϖ : K) ≠ 0)
    (harch : ∀ k : ℕ, ∃ n : ℕ, δ ^ n ≤ Valued.v (ϖ : K) ^ k) :
    ∀ k : ℕ, ∃ n : ℕ, 𝔪 ^ n ≤ (Ideal.span {ϖ} ^ k).comap ev := by p2m_exact_reverting @_root_.P2MW.S_Valued_forall_exists_pow_le_comap_span_singleton_pow_of_eq_span.solution
