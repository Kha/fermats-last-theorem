import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem

set_option autoImplicit false

universe u

theorem WittVector.exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem
    {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (σ : R →+* R)
    (hσ : ∀ a : R, σ a - a ^ p ∈ Ideal.span {(p : R)})
    (n : ℕ) (g : ℕ → R)
    (hg : ∀ k : ℕ, k + 1 < n → g (k + 1) - σ (g k) ∈ Ideal.span {(p : R) ^ (k + 1)}) :
    ∃ x : WittVector p R, ∀ k < n, WittVector.ghostComponent k x = g k := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem.solution
