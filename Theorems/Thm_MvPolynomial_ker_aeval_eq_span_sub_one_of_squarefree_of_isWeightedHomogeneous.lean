import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous

theorem MvPolynomial.ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous
    {K : Type*} [Field K] {N : ℕ} (hN : 0 < N) {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    {Q R : PowerSeries K} (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hR0 : PowerSeries.constantCoeff R = 1) (hQR : Q ^ 3 ≠ R ^ 2)
    {A : MvPolynomial (Fin 2) K}
    (hA : A.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) N) (hsq : Squarefree A)
    (hA1 : MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K) A = 1) :
    RingHom.ker (MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K)).toRingHom =
      Ideal.span {A - 1} := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous.solution
