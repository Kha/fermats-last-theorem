import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_tensorProduct_eq_zero_of_forall_lift_points_eq_zero

set_option autoImplicit false
open scoped TensorProduct

theorem HopfAlgebra.tensorProduct_eq_zero_of_forall_lift_points_eq_zero
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
    x = 0 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_tensorProduct_eq_zero_of_forall_lift_points_eq_zero.solution
