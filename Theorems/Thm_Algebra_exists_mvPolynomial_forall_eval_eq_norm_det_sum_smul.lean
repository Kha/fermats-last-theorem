import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul

set_option autoImplicit false

theorem Algebra.exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul
    (E : Type) [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
    (m : Type) [Fintype m] [DecidableEq m]
    (n : ℕ) (e : Fin n → Matrix m m E) :
    ∃ P : MvPolynomial (Fin n) ℝ, ∀ c : Fin n → ℝ,
      MvPolynomial.eval c P = Algebra.norm ℝ (Matrix.det (∑ a, c a • e a)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul.solution
