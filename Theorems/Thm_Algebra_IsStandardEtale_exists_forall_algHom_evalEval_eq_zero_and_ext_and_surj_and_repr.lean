import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsStandardEtale_exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr

set_option autoImplicit false

open Polynomial
open scoped Polynomial.Bivariate

theorem Algebra.IsStandardEtale.exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr
    (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A]
    [Algebra.IsStandardEtale k[X] A] :
    ∃ (x : A) (F G : k[X][Y]),
      (∀ τ : A →ₐ[k] k,
        Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) F = 0 ∧
        Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) G ≠ 0 ∧
        Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) (Polynomial.derivative F) ≠ 0) ∧
      (∀ τ τ' : A →ₐ[k] k, τ (algebraMap k[X] A Polynomial.X) = τ' (algebraMap k[X] A Polynomial.X) → τ x = τ' x → τ = τ') ∧
      (∀ z w : k, Polynomial.evalEval z w F = 0 → Polynomial.evalEval z w G ≠ 0 →
        ∃ τ : A →ₐ[k] k, τ (algebraMap k[X] A Polynomial.X) = z ∧ τ x = w) ∧
      (∀ s : A, ∃ (h : k[X][Y]) (n : ℕ), ∀ τ : A →ₐ[k] k,
        τ s * (Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) G) ^ n =
          Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) h) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsStandardEtale_exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr.solution
