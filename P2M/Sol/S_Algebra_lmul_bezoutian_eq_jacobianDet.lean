import Mathlib
import Theorems.Thm_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul
import P2M.Util
namespace P2MW.S_Algebra_lmul_bezoutian_eq_jacobianDet

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) :
    Algebra.TensorProduct.lmul' R
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a))) =
      Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i))) := by
  classical

  have hcomm : (Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) R).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))) =
      (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))).comp (Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) R) R) := by
    ext x
    · simp
    · simp
  have h := DFunLike.congr_fun hcomm (Matrix.det (Matrix.of a))
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h
  rw [h, Ideal.Quotient.mkₐ_eq_mk]
  congr 1

  rw [show Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) R) R (Matrix.det (Matrix.of a)) =
      ((Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) R) R : MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R) : MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R →+* MvPolynomial (Fin m) R) (Matrix.det (Matrix.of a)) from rfl,
    RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact MvPolynomial.lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul R (f i) (a i) (ha i) j
