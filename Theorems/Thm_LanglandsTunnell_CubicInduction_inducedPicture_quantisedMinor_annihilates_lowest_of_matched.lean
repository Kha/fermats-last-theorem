import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_inducedPicture_quantisedMinor_annihilates_lowest_of_matched

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.inducedPicture_quantisedMinor_annihilates_lowest_of_matched
    (τ τ₃ : ℝ) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    let δ : (Fin 3 → ℂ) → ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c' f => act ν 0 1 (act ν 1 2 f) - act ν 0 2 (act ν 1 1 f) - MvPolynomial.C c' * act ν 0 2 f
    let ν₁₂ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, 1 / 2 + τ * Complex.I, τ₃ * Complex.I]
    let ν₁₃ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, τ₃ * Complex.I, 1 / 2 + τ * Complex.I]
    let c' : ℂ := 1 / 2 - τ * Complex.I
    let IsOrthogonal : (Fin 3 × Fin 3 → ℂ) → Prop :=
      fun k => ∀ i j : Fin 3, ∑ a : Fin 3, k (i, a) * k (j, a) = if i = j then 1 else 0
    (∀ k : Fin 3 × Fin 3 → ℂ, IsOrthogonal k →
      MvPolynomial.eval k (δ ν₁₂ c' (1 : MvPolynomial (Fin 3 × Fin 3) ℂ)) = 0) ∧
    (∀ k : Fin 3 × Fin 3 → ℂ, IsOrthogonal k → ∀ j : Fin 3,
      MvPolynomial.eval k (δ ν₁₂ c' (MvPolynomial.X (2, j))) = 0) ∧
    (∀ k : Fin 3 × Fin 3 → ℂ, IsOrthogonal k →
      MvPolynomial.eval k (δ ν₁₃ c' (1 : MvPolynomial (Fin 3 × Fin 3) ℂ)) = 0) ∧
    (∀ k : Fin 3 × Fin 3 → ℂ, IsOrthogonal k → ∀ j : Fin 3,
      MvPolynomial.eval k (δ ν₁₃ c' (MvPolynomial.X (1, j))) = 0) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_inducedPicture_quantisedMinor_annihilates_lowest_of_matched.solution
