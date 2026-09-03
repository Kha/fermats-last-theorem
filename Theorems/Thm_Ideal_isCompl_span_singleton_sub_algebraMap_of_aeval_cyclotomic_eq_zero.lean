import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_isCompl_span_singleton_sub_algebraMap_of_aeval_cyclotomic_eq_zero

set_option autoImplicit false

open Polynomial Classical in

theorem Ideal.isCompl_span_singleton_sub_algebraMap_of_aeval_cyclotomic_eq_zero
    (A : Type) [CommRing A] [IsDomain A] (B : Type) [CommRing B] [Algebra A B]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓA : IsUnit ((ℓ : ℕ) : A)) (hω : ∃ ω : A, IsPrimitiveRoot ω ℓ)
    (ξ : B) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic ℓ A) = 0)
    (a : A) (ha : a ^ ℓ = 1) (ha1 : a ≠ 1) :
    IsCompl (Ideal.span {ξ - algebraMap A B a})
      (Ideal.span {∏ μ ∈ (primitiveRoots ℓ A).erase a, (ξ - algebraMap A B μ)}) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_isCompl_span_singleton_sub_algebraMap_of_aeval_cyclotomic_eq_zero.solution
