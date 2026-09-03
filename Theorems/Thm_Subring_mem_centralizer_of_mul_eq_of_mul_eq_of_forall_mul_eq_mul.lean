import Mathlib
import P2M.Util
import P2M.Sol.S_Subring_mem_centralizer_of_mul_eq_of_mul_eq_of_forall_mul_eq_mul

set_option autoImplicit false

theorem Subring.mem_centralizer_of_mul_eq_of_mul_eq_of_forall_mul_eq_mul
    {R : Type*} [Ring R] (S : Set R) (ε ε' δ : R)
    (hε : ε ∈ Subring.centralizer S) (h₁ : ε * ε' = δ) (h₂ : ε' * ε = δ)
    (hδ : ∀ x : R, δ * x = x * δ) (hcanc : ∀ x y : R, δ * x = δ * y → x = y) :
    ε' ∈ Subring.centralizer S := by p2m_exact_reverting @_root_.P2MW.S_Subring_mem_centralizer_of_mul_eq_of_mul_eq_of_forall_mul_eq_mul.solution
