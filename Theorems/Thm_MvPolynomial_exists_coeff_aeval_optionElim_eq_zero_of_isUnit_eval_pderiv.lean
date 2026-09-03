import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_coeff_aeval_optionElim_eq_zero_of_isUnit_eval_pderiv
set_option autoImplicit false

theorem MvPolynomial.exists_coeff_aeval_optionElim_eq_zero_of_isUnit_eval_pderiv
    {A : Type*} [CommRing A] (m : ℕ) (u : A) (w0 : Fin 2 → A) (G : Fin 2 → MvPolynomial (Option (Fin 2)) A)
    (hvars : (some 1 : Option (Fin 2)) ∉ (G 0).vars)
    (hroot : ∀ j, MvPolynomial.eval (fun o => Option.elim o u w0) (G j) = 0)
    (hder : ∀ j, IsUnit (MvPolynomial.eval (fun o => Option.elim o u w0) (MvPolynomial.pderiv (some j) (G j)))) :
    ∃ w : Fin 2 → Fin (m + 1) → A, (∀ j, w j 0 = w0 j) ∧
      ∀ (j : Fin 2) (r : Fin (m + 1)),
        (MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (G j)).coeff r = 0 := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_coeff_aeval_optionElim_eq_zero_of_isUnit_eval_pderiv.solution
