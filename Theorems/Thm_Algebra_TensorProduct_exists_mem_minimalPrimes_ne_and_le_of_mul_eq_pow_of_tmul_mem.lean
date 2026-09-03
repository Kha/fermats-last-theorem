import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.TensorProduct.exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem
    (R : Type*) [CommRing R] (π : R) (hπ : (Ideal.span {π}).IsMaximal)
    (𝒪 : Type*) [CommRing 𝒪] [Algebra R 𝒪] (hπ𝒪 : algebraMap R 𝒪 π ∈ nonZeroDivisors 𝒪)
    (κ : Type*) [Field κ] [Algebra R κ] (hπκ : algebraMap R κ π = 0)
    [IsReduced (κ ⊗[R] 𝒪)]
    (v v' : 𝒪) (n : ℕ) (hvv' : v * v' = algebraMap R 𝒪 π ^ n)
    (Q₀ 𝔮 : Ideal (κ ⊗[R] 𝒪)) (hQ₀ : Q₀ ∈ minimalPrimes (κ ⊗[R] 𝒪)) [𝔮.IsPrime] (hle : Q₀ ≤ 𝔮)
    (hv₀ : (1 : κ) ⊗ₜ[R] v ∉ Q₀) (hv : (1 : κ) ⊗ₜ[R] v ∈ 𝔮) :
    ∃ Q₁ ∈ minimalPrimes (κ ⊗[R] 𝒪), Q₁ ≠ Q₀ ∧ Q₁ ≤ 𝔮 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem.solution
