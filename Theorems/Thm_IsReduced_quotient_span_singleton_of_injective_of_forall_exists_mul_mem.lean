import Mathlib
import P2M.Util
import P2M.Sol.S_IsReduced_quotient_span_singleton_of_injective_of_forall_exists_mul_mem

theorem IsReduced.quotient_span_singleton_of_injective_of_forall_exists_mul_mem
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) (p : A)
    [IsReduced (B ⧸ Ideal.span {algebraMap A B p})]
    (S : Set A)
    (hS : ∀ b : B, ∃ s ∈ S, ∃ a : A, algebraMap A B a = algebraMap A B s * b)
    (htf : ∀ s ∈ S, ∀ a : A, s * a ∈ Ideal.span {p} → a ∈ Ideal.span {p}) :
    IsReduced (A ⧸ Ideal.span {p}) := by p2m_exact_reverting @_root_.P2MW.S_IsReduced_quotient_span_singleton_of_injective_of_forall_exists_mul_mem.solution
