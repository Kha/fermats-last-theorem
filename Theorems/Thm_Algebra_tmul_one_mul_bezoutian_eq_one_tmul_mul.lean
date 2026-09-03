import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_tmul_one_mul_bezoutian_eq_one_tmul_mul

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.tmul_one_mul_bezoutian_eq_one_tmul_mul
    (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j))
    (s : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) :
    (s ⊗ₜ[R] (1 : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))) *
        Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a)) =
      ((1 : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) ⊗ₜ[R] s) *
        Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_tmul_one_mul_bezoutian_eq_one_tmul_mul.solution
