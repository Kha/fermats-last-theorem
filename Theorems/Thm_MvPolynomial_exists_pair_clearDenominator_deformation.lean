import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_pair_clearDenominator_deformation

set_option autoImplicit false

theorem MvPolynomial.exists_pair_clearDenominator_deformation
    (r b₁ b₂ ω c : ℂ) (hr : r ≠ 0) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hω : ω ≠ 0)
    (P : MvPolynomial (Fin 3) ℂ) (D₁ D₂ : Polynomial ℂ) (e : ℕ)
    (hD₁ : D₁.eval 0 ≠ 0) (hD₂ : D₂.eval 0 ≠ 0) :
    ∃ p q : MvPolynomial (Fin 2) ℂ,
      (∀ y : ℂ, y ≠ 0 → ∃ x : ℂ, MvPolynomial.eval ![x, y] q ≠ 0) ∧
      ∀ (x y Z : ℂ), y ≠ 0 →
        Z * (D₁.eval (b₁ * y⁻¹ * (r * x)) * D₁.eval (b₂ * y * (r * x)) * D₂.eval (ω * (r * x) ^ 2) *
            (ω * (r * x) ^ 2) ^ e) =
          c * MvPolynomial.eval ![r * x, b₁ * y⁻¹, b₂ * y] P →
        Z * MvPolynomial.eval ![x, y] q = MvPolynomial.eval ![x, y] p := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_pair_clearDenominator_deformation.solution
