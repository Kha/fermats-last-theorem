import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_not_isMaximal_of_mem_minimalPrimes_of_forall_not_isOpen_singleton

set_option autoImplicit false

open TensorProduct

theorem Ideal.not_isMaximal_of_mem_minimalPrimes_of_forall_not_isOpen_singleton
    {R : Type*} [CommRing R] {κ : Type*} [Field κ] [Algebra R κ]
    (ϖ : R) (hϖ : algebraMap R κ ϖ = 0) (hmax : (Ideal.span {ϖ}).IsMaximal)
    {B : Type*} [CommRing B] [Algebra R B] [Algebra.FiniteType R B] (b : B) (hb : b = algebraMap R B ϖ)
    (hiso : ∀ z : PrimeSpectrum (B ⊗[R] κ), ¬ IsOpen ({z} : Set (PrimeSpectrum (B ⊗[R] κ))))
    (Q : Ideal (B ⧸ Ideal.span {b})) (hQ : Q ∈ minimalPrimes (B ⧸ Ideal.span {b})) :
    ¬ Q.IsMaximal := by p2m_exact_reverting @_root_.P2MW.S_Ideal_not_isMaximal_of_mem_minimalPrimes_of_forall_not_isOpen_singleton.solution
