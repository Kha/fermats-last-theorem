import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_lmul_bezoutian_eq_jacobianDet

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.lmul_bezoutian_eq_jacobianDet
    (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) :
    Algebra.TensorProduct.lmul' R
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a))) =
      Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i))) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_lmul_bezoutian_eq_jacobianDet.solution
