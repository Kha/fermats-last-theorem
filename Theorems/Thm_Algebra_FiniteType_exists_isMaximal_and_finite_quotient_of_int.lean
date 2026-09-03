import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FiniteType_exists_isMaximal_and_finite_quotient_of_int

set_option autoImplicit false

theorem Algebra.FiniteType.exists_isMaximal_and_finite_quotient_of_int
    (R : Type) [CommRing R] [Algebra ℤ R] [Nontrivial R] [Algebra.FiniteType ℤ R] :
    ∃ 𝔪 : Ideal R, 𝔪.IsMaximal ∧ Finite (R ⧸ 𝔪) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FiniteType_exists_isMaximal_and_finite_quotient_of_int.solution
