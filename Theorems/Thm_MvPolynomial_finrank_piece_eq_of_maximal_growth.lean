import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import P2M.Util
import P2M.Sol.S_MvPolynomial_finrank_piece_eq_of_maximal_growth

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor

theorem MvPolynomial.finrank_piece_eq_of_maximal_growth
    (n m : ℕ) (h : ℕ → ℕ)
    (h₂ : ∀ e, m ≤ e → ∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))
    (h₃ : ∀ e, m ≤ e → ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J e) = h e ∧ Module.finrank K (piece J (e + 1)) = h (e + 1))
    (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hm : Module.finrank K (piece J m) = h m) (hm₁ : Module.finrank K (piece J (m + 1)) = h (m + 1)) :
    ∀ e, m ≤ e → Module.finrank K (piece J e) = h e := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_finrank_piece_eq_of_maximal_growth.solution
