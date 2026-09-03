import Mathlib
import P2M.Util
import P2M.Sol.S_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul

theorem HexagonalLattice.summable_thetaTerm_and_tsum_neg_inv_three_mul (σ : ℂ) (hσ : 0 < σ.im) :
    Summable (fun p : ℤ × ℤ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * σ *
        ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2))) ∧
    (∑' p : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-1 / (3 * σ)) *
        ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2))) =
      -Complex.I * (Real.sqrt 3 : ℂ) * σ *
        ∑' p : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * σ *
          ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2)) := by p2m_exact_reverting @_root_.P2MW.S_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul.solution
