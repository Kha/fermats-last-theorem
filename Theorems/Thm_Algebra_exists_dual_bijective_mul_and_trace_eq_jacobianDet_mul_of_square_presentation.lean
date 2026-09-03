import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_presentation

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_presentation
    (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    [Module.Finite R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))]
    [Module.Free R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))] :
    ∃ τ : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) →ₗ[R] R,
      Function.Bijective (fun a : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f) =>
        τ.comp (LinearMap.mulLeft R a)) ∧
      ∀ a : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f),
        Algebra.trace R _ a =
          τ (Ideal.Quotient.mk (Ideal.span (Set.range f))
              (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i))) * a) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_presentation.solution
