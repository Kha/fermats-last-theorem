import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ e : ℕ, D₀ ≤ e →
      (∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
        (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
        (Module.finrank K (piece J e) : ℚ) = P.eval (e : ℚ) →
        (Module.finrank K (piece J (e + 1)) : ℚ) ≤ P.eval ((e : ℚ) + 1)) ∧
      ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
        (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
        (Module.finrank K (piece J e) : ℚ) = P.eval (e : ℚ) ∧
        (Module.finrank K (piece J (e + 1)) : ℚ) = P.eval ((e : ℚ) + 1) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval.solution
