import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_forall_eval_eq_zero_of_isUnit_det_jacobian
set_option autoImplicit false

theorem ValuationSubring.exists_forall_eval_eq_zero_of_isUnit_det_jacobian
    {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K)
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (F : σ → MvPolynomial σ A) (P₀ : σ → A)
    (hF : ∀ i, MvPolynomial.eval P₀ (F i) ∈ IsLocalRing.maximalIdeal A)
    (hJ : IsUnit (Matrix.det (Matrix.of fun i j : σ => MvPolynomial.eval P₀ (MvPolynomial.pderiv j (F i))))) :
    ∃ P : σ → A, (∀ i, P i - P₀ i ∈ IsLocalRing.maximalIdeal A) ∧ ∀ i, MvPolynomial.eval P (F i) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_forall_eval_eq_zero_of_isUnit_det_jacobian.solution
