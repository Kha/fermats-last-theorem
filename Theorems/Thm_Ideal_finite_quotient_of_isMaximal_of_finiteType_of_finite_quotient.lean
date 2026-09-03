import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient

set_option autoImplicit false

theorem Ideal.finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient
    (A : Type) [CommRing A] (𝔪 : Ideal A) [𝔪.IsMaximal] [Finite (A ⧸ 𝔪)]
    (B : Type) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (𝔭 : Ideal B) [𝔭.IsMaximal] (h𝔪 : Ideal.map (algebraMap A B) 𝔪 ≤ 𝔭) :
    Finite (B ⧸ 𝔭) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient.solution
