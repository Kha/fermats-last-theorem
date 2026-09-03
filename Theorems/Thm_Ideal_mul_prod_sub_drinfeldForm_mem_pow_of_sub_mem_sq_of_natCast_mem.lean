import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem

set_option autoImplicit false

theorem Ideal.mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] (𝔪 : Ideal R) (hq : ((q : ℕ) : R) ∈ 𝔪)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ 𝔪) (hx₁ : x₁ ∈ 𝔪)
    (P : ZMod q → R) (hP : ∀ c : ZMod q, P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ 𝔪 ^ 2) :
    x₀ * (∏ c : ZMod q, P c) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ 𝔪 ^ (q + 2) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem.solution
