import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_isSquare_or_isSquare_of_isHomogeneous_of_forall_eval_mul_eq

set_option autoImplicit false

theorem MvPolynomial.isSquare_or_isSquare_of_isHomogeneous_of_forall_eval_mul_eq
    (D c : ℤ) (hD : 0 < D) (hc : 0 < c)
    (F : (Fin 4 → ℤ) → ℕ) (P : MvPolynomial (Fin 4) ℚ) (hP : P.IsHomogeneous 4)
    (hF : ∀ v : Fin 4 → ℤ, (F v : ℚ) = MvPolynomial.eval (fun i => (v i : ℚ)) P)
    (hone : F ![1, 0, 0, 0] = 1)
    (hmul : ∀ v w : Fin 4 → ℤ,
      F ![v 0 * w 0 + D * (v 1 * w 1) + c * (v 2 * w 2) + D * c * (v 3 * w 3),
          v 0 * w 1 + v 1 * w 0 + c * (v 2 * w 3 + v 3 * w 2),
          v 0 * w 2 + v 2 * w 0 + D * (v 1 * w 3 + v 3 * w 1),
          v 0 * w 3 + v 3 * w 0 + v 1 * w 2 + v 2 * w 1] = F v * F w)
    (hzd : ∀ r : ℤ, r ^ 2 = D * c → F ![r, 0, 0, 1] = 0) :
    IsSquare D ∨ IsSquare c := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_isSquare_or_isSquare_of_isHomogeneous_of_forall_eval_mul_eq.solution
