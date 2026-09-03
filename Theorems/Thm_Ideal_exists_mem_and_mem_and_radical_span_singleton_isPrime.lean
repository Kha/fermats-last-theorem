import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime

set_option autoImplicit false

universe u v

theorem Ideal.exists_mem_and_mem_and_radical_span_singleton_isPrime
    (k : Type u) [Field k] [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : 2 ≤ ringKrullDim A)
    (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal] (hne : m₀ ≠ m₁) :
    ∃ f : A, f ∈ m₀ ∧ f ∈ m₁ ∧ f ≠ 0 ∧ (Ideal.span {f}).radical.IsPrime := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime.solution
