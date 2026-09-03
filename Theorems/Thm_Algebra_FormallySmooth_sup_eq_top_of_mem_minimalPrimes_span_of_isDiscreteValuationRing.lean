import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_sup_eq_top_of_mem_minimalPrimes_span_of_isDiscreteValuationRing

set_option autoImplicit false

theorem Algebra.FormallySmooth.sup_eq_top_of_mem_minimalPrimes_span_of_isDiscreteValuationRing
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [Algebra A B]
    [Algebra.FormallySmooth A B] [Algebra.FiniteType A B]
    (ϖ : A) (hϖ : Irreducible ϖ)
    (P P' : Ideal B) (hP : P ∈ (Ideal.span {algebraMap A B ϖ}).minimalPrimes)
    (hP' : P' ∈ (Ideal.span {algebraMap A B ϖ}).minimalPrimes) (hne : P ≠ P') :
    P ⊔ P' = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_sup_eq_top_of_mem_minimalPrimes_span_of_isDiscreteValuationRing.solution
