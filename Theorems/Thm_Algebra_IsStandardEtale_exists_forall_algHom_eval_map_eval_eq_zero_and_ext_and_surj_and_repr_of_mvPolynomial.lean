import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial

set_option autoImplicit false

open Polynomial

theorem Algebra.IsStandardEtale.exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial
    (k : Type) [Field k] {n : ℕ} (A : Type) [CommRing A] [Algebra k A] [Algebra (MvPolynomial (Fin n) k) A]
    [IsScalarTower k (MvPolynomial (Fin n) k) A] [Algebra.IsStandardEtale (MvPolynomial (Fin n) k) A] :
    ∃ (x : A) (F G : Polynomial (MvPolynomial (Fin n) k)),
      (∀ τ : A →ₐ[k] k,
        (F.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) = 0 ∧
        (G.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) ≠ 0 ∧
        ((Polynomial.derivative F).map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) ≠ 0) ∧
      (∀ τ τ' : A →ₐ[k] k,
        (∀ i : Fin n, τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)) =
          τ' (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i))) → τ x = τ' x → τ = τ') ∧
      (∀ (z : Fin n → k) (w : k), (F.map (MvPolynomial.eval z)).eval w = 0 → (G.map (MvPolynomial.eval z)).eval w ≠ 0 →
        ∃ τ : A →ₐ[k] k, (∀ i : Fin n, τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)) = z i) ∧ τ x = w) ∧
      (∀ s : A, ∃ (h : Polynomial (MvPolynomial (Fin n) k)) (N : ℕ), ∀ τ : A →ₐ[k] k,
        τ s * ((G.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x)) ^ N =
          (h.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial.solution
