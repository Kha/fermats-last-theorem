import Mathlib
import P2M.Util
import P2M.Sol.S_Module_forall_eq_zero_and_mem_range_of_isWeaklyRegular_complex

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.forall_eq_zero_and_mem_range_of_isWeaklyRegular_complex
    (R : Type u) [CommRing R] (rs : List R)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    (hreg : ∀ i, RingTheory.Sequence.IsWeaklyRegular (K i) rs)
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (htors0 : ∃ N : ℕ, ∀ a ∈ Ideal.ofList rs ^ N, ∀ z : K 0, δ 0 z = 0 → a • z = 0)
    (htors : ∀ i, ∃ N : ℕ, ∀ a ∈ Ideal.ofList rs ^ N, ∀ z : K (i + 1), δ (i + 1) z = 0 →
      a • z ∈ LinearMap.range (δ i)) :
    (0 < rs.length → ∀ z : K 0, δ 0 z = 0 → z = 0) ∧
      ∀ i : ℕ, i + 1 < rs.length → ∀ z : K (i + 1), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i) := by p2m_exact_reverting @_root_.P2MW.S_Module_forall_eq_zero_and_mem_range_of_isWeaklyRegular_complex.solution
