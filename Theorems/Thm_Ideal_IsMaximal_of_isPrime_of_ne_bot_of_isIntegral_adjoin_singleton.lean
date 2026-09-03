import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_IsMaximal_of_isPrime_of_ne_bot_of_isIntegral_adjoin_singleton

set_option autoImplicit false

theorem Ideal.IsMaximal.of_isPrime_of_ne_bot_of_isIntegral_adjoin_singleton
    (R : Type) [CommRing R] (D : Type) [CommRing D] [IsDomain D] [Algebra R D]
    (hR : ∀ r : R, algebraMap R D r = 0 ∨ IsUnit (algebraMap R D r))
    (x : D) (hint : ∀ d : D, IsIntegral (Algebra.adjoin R ({x} : Set D)) d)
    (P : Ideal D) [P.IsPrime] (hP : P ≠ ⊥) :
    P.IsMaximal := by p2m_exact_reverting @_root_.P2MW.S_Ideal_IsMaximal_of_isPrime_of_ne_bot_of_isIntegral_adjoin_singleton.solution
