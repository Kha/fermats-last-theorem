import Mathlib
import P2M.Util
import P2M.Sol.S_IsPrimitiveRoot_exists_tmul_sub_tmul_mem_of_aeval_cyclotomic_eq_zero

set_option autoImplicit false

open scoped TensorProduct

theorem IsPrimitiveRoot.exists_tmul_sub_tmul_mem_of_aeval_cyclotomic_eq_zero
    (q : ℕ) [Fact q.Prime]
    (Z₀ : Type) [CommRing Z₀]
    (C : Type) [CommRing C] [Algebra Z₀ C] (w : C) (hw : Polynomial.aeval w (Polynomial.cyclotomic q Z₀) = 0)
    (A : Type) [CommRing A] [IsDomain A] [Algebra Z₀ A] (ζ : A) (hζ : IsPrimitiveRoot ζ q) :
    (∏ μ ∈ primitiveRoots q A, ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C)) = 0) ∧
    (∀ 𝔭 : Ideal (TensorProduct Z₀ A C), 𝔭.IsPrime →
      ∃ μ ∈ primitiveRoots q A, ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C)) ∈ 𝔭) ∧
    (∀ (𝔭 : Ideal (TensorProduct Z₀ A C)) (μ μ' : A),
      ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C)) ∈ 𝔭 →
      ((μ' ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C)) ∈ 𝔭 →
        ((μ - μ') ⊗ₜ[Z₀] (1 : C) : (TensorProduct Z₀ A C)) ∈ 𝔭) ∧
    (∀ (𝔭 : Ideal (TensorProduct Z₀ A C)) (μ : A), 𝔭 ∈ minimalPrimes (TensorProduct Z₀ A C) →
      ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C)) ∈ 𝔭 →
        𝔭.map (Ideal.Quotient.mk (Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C))})) ∈
          minimalPrimes ((TensorProduct Z₀ A C) ⧸ Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C))}) ∧
        Nonempty (((TensorProduct Z₀ A C) ⧸ 𝔭) ≃+*
          (((TensorProduct Z₀ A C) ⧸ Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C))}) ⧸
            𝔭.map (Ideal.Quotient.mk (Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : (TensorProduct Z₀ A C))}))))) := by p2m_exact_reverting @_root_.P2MW.S_IsPrimitiveRoot_exists_tmul_sub_tmul_mem_of_aeval_cyclotomic_eq_zero.solution
