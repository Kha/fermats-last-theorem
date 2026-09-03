import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FiniteType_finite_quotient_and_exists_charP_of_isMaximal_int

set_option autoImplicit false

theorem Algebra.FiniteType.finite_quotient_and_exists_charP_of_isMaximal_int
    (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] (𝔮 : Ideal A) [𝔮.IsMaximal] :
    Finite (A ⧸ 𝔮) ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ CharP (A ⧸ 𝔮) ℓ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FiniteType_finite_quotient_and_exists_charP_of_isMaximal_int.solution
