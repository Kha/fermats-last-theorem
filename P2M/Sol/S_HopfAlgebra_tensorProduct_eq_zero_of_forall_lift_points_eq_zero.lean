import Mathlib
import Theorems.Thm_Algebra_TensorProduct_eq_zero_of_forall_lift_apply_eq_zero
import P2M.Util
namespace P2MW.S_HopfAlgebra_tensorProduct_eq_zero_of_forall_lift_points_eq_zero

set_option autoImplicit false
open scoped TensorProduct

theorem solution
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]
    [Module.Finite ↥(IntermediateField.fixedField D) A]
    [Finite (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
        (Pi.algHom ↥(IntermediateField.fixedField D) _
          fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) =>
            (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A →ₐ[AlgebraicClosure ℚ]
          (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)))
    (x : A ⊗[↥(IntermediateField.fixedField D)] A)
    (hx : ∀ ν ν' : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ,
      Algebra.TensorProduct.lift ν ν' (fun _ _ => Commute.all _ _) x = 0) :
    x = 0 :=
  Algebra.TensorProduct.eq_zero_of_forall_lift_apply_eq_zero
    (fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) =>
      (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
    hev.1 x (fun p q =>
      hx (WithConv.ofConv p : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)
        (WithConv.ofConv q : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
