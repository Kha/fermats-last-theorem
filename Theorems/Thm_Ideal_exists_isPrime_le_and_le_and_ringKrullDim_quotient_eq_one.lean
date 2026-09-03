import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one

set_option autoImplicit false

universe u v

theorem Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
    (k : Type u) [Field k] [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : 1 ≤ ringKrullDim A)
    (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal] :
    ∃ P : Ideal A, P.IsPrime ∧ P ≤ m₀ ∧ P ≤ m₁ ∧ ringKrullDim (A ⧸ P) = 1 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.solution
