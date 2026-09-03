import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow

theorem MvPolynomial.finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow
    (p : ℕ) (hp : 0 < p) (n a b : ℕ) (hab : a < b) :
    Finite (MvPolynomial Bool ℤ ⧸ Ideal.span
        ({MvPolynomial.X true * MvPolynomial.X false - MvPolynomial.C (p : ℤ),
          MvPolynomial.X false ^ n, MvPolynomial.X true ^ b - MvPolynomial.X true ^ a} :
          Set (MvPolynomial Bool ℤ))) ∧
      Nat.card (MvPolynomial Bool ℤ ⧸ Ideal.span
        ({MvPolynomial.X true * MvPolynomial.X false - MvPolynomial.C (p : ℤ),
          MvPolynomial.X false ^ n, MvPolynomial.X true ^ b - MvPolynomial.X true ^ a} :
          Set (MvPolynomial Bool ℤ))) ≤ p ^ (n * b) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow.solution
