import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_squarefree_of_isWeightedHomogeneous_of_aeval_eq_one

theorem MvPolynomial.squarefree_of_isWeightedHomogeneous_of_aeval_eq_one
    {K : Type*} [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (h5 : 5 ≤ ℓ)
    {P Q R : PowerSeries K}
    (hP0 : PowerSeries.constantCoeff P = 1) (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hR0 : PowerSeries.constantCoeff R = 1) (hQR : Q ^ 3 ≠ R ^ 2)
    (hP : 12 * (PowerSeries.X * PowerSeries.derivative K P) = P ^ 2 - Q)
    (hQ : 3 * (PowerSeries.X * PowerSeries.derivative K Q) = P * Q - R)
    (hR : 2 * (PowerSeries.X * PowerSeries.derivative K R) = P * R - Q ^ 2)
    {A : MvPolynomial (Fin 2) K}
    (hA : A.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) (ℓ - 1))
    (hA1 : MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K) A = 1) :
    Squarefree A := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_squarefree_of_isWeightedHomogeneous_of_aeval_eq_one.solution
