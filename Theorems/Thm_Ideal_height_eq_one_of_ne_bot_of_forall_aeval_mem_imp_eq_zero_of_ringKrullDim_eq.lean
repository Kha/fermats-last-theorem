import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq

set_option autoImplicit false

universe u v

theorem Ideal.height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq
    (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥)
    (d : ℕ) (hd : ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim A)
    (f : Fin d → A) (hind : ∀ Q : MvPolynomial (Fin d) k, MvPolynomial.aeval f Q ∈ p → Q = 0) :
    p.height = 1 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq.solution
