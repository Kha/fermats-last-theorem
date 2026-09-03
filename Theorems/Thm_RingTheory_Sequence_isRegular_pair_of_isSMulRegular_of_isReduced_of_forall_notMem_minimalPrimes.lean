import Mathlib
import P2M.Util
import P2M.Sol.S_RingTheory_Sequence_isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes

set_option autoImplicit false

theorem RingTheory.Sequence.isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes
    {A : Type*} [CommRing A] [IsLocalRing A] {B : Type*} [CommRing B] [Nontrivial B] [Algebra A B] [Module.Finite A B]
    (a b : A) (ha𝔪 : a ∈ IsLocalRing.maximalIdeal A) (hb𝔪 : b ∈ IsLocalRing.maximalIdeal A)
    (ha : IsSMulRegular B (algebraMap A B a))
    (hred : IsReduced (B ⧸ Ideal.span {algebraMap A B a}))
    (hb : ∀ P ∈ minimalPrimes (B ⧸ Ideal.span {algebraMap A B a}),
      Ideal.Quotient.mk (Ideal.span {algebraMap A B a}) (algebraMap A B b) ∉ P) :
    RingTheory.Sequence.IsRegular B [a, b] := by p2m_exact_reverting @_root_.P2MW.S_RingTheory_Sequence_isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes.solution
