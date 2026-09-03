import Mathlib
import P2M.Util
namespace P2MW.S_IsLocalRing_isReduced_residueField_tensorProduct_iff_of_maximalIdeal_eq_span

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem solution
    {A : Type*} [CommRing A] [IsLocalRing A] (a : A) (ha : maximalIdeal A = Ideal.span {a})
    (R : Type*) [CommRing R] [Algebra A R] :
    IsReduced (ResidueField A ⊗[A] R) ↔ IsReduced (R ⧸ Ideal.span {algebraMap A R a}) := by
  have hI : (maximalIdeal A).map (algebraMap A R) = Ideal.span {algebraMap A R a} := by
    rw [ha, Ideal.map_span, Set.image_singleton]
  let e : ResidueField A ⊗[A] R ≃+* R ⧸ Ideal.span {algebraMap A R a} :=
    ((Algebra.TensorProduct.comm A (ResidueField A) R).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (maximalIdeal A)).symm.restrictScalars A)).toRingEquiv.trans (Ideal.quotEquivOfEq hI)
  exact ⟨fun _ => isReduced_of_injective e.symm e.symm.injective,
    fun _ => isReduced_of_injective e e.injective⟩
