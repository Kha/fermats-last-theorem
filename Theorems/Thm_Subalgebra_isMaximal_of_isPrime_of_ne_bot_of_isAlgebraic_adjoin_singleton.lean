import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_isMaximal_of_isPrime_of_ne_bot_of_isAlgebraic_adjoin_singleton

universe u v

theorem Subalgebra.isMaximal_of_isPrime_of_ne_bot_of_isAlgebraic_adjoin_singleton
    {A : Type u} [CommRing A] {F : Type v} [Field F] [Algebra A F]
    (t : F) [Algebra.IsAlgebraic ↥(Algebra.adjoin A ({t} : Set F)) F]
    (S : Subalgebra A F) (hS : ∀ a : A, algebraMap A F a ≠ 0 → (algebraMap A F a)⁻¹ ∈ S)
    (P : Ideal ↥S) [P.IsPrime] (hP : P ≠ ⊥) : P.IsMaximal := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_isMaximal_of_isPrime_of_ne_bot_of_isAlgebraic_adjoin_singleton.solution
