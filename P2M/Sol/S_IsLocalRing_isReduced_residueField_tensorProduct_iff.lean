import Mathlib
import P2M.Util
namespace P2MW.S_IsLocalRing_isReduced_residueField_tensorProduct_iff

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem solution
    {A : Type*} [CommRing A] [IsLocalRing A]
    (R : Type*) [CommRing R] [Algebra A R] :
    IsReduced (ResidueField A ⊗[A] R) ↔ IsReduced (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by
  let e : ResidueField A ⊗[A] R ≃ₐ[A] R ⧸ (maximalIdeal A).map (algebraMap A R) :=
    (Algebra.TensorProduct.comm A (ResidueField A) R).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (maximalIdeal A)).symm.restrictScalars A)
  exact ⟨fun _ => isReduced_of_injective e.symm e.symm.injective,
    fun _ => isReduced_of_injective e e.injective⟩
