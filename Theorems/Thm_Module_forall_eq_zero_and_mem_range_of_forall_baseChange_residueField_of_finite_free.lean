import Mathlib
import P2M.Util
import P2M.Sol.S_Module_forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (hbdd : ∀ i, n < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (h0 : ∀ z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K 0,
      (δ 0).baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 → z = 0)
    (hS : ∀ (i : ℕ) (z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K (i + 1)),
      (δ (i + 1)).baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 →
        z ∈ LinearMap.range ((δ i).baseChange (R ⧸ IsLocalRing.maximalIdeal R))) :
    (∀ z : K 0, δ 0 z = 0 → z = 0) ∧
      ∀ (i : ℕ) (z : K (i + 1)), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i) := by p2m_exact_reverting @_root_.P2MW.S_Module_forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free.solution
