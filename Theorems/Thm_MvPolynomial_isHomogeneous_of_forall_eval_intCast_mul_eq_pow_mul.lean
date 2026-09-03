import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul

set_option autoImplicit false

theorem MvPolynomial.isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {ι : Type*} (P : MvPolynomial ι R) (d : ℕ)
    (h : ∀ (n : ℤ) (c : ι → ℤ), MvPolynomial.eval (fun i => ((n * c i : ℤ) : R)) P =
      (n : R) ^ d * MvPolynomial.eval (fun i => (c i : R)) P) :
    P.IsHomogeneous d := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul.solution
