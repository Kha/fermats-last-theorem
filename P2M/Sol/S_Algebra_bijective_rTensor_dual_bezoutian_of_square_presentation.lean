import Mathlib
import Theorems.Thm_Algebra_bijective_rTensor_dual_bezoutian_of_forall_field
import Theorems.Thm_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed
import P2M.Util
namespace P2MW.S_Algebra_bijective_rTensor_dual_bezoutian_of_square_presentation

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    [Module.Finite R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))]
    [Module.Free R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))]
    (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) :
    Function.Bijective (fun φ : Module.Dual R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) =>
      TensorProduct.lid R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))
        (LinearMap.rTensor (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
            (Matrix.det (Matrix.of a))))) := by
  exact Algebra.bijective_rTensor_dual_bezoutian_of_forall_field R f a ha
    (fun K _ _ g _ b hb => Algebra.bijective_rTensor_dual_bezoutian_of_isAlgClosed K g b hb)
