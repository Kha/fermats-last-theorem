import Mathlib
import Theorems.Thm_Algebra_isReduced_tensorProduct_of_perfectField
import P2M.Util
namespace P2MW.S_Algebra_TensorProduct_isReduced_residueField_tensorProduct_of_perfectField

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem solution
    (A' : Type*) [CommRing A'] [IsLocalRing A'] [PerfectField (ResidueField A')]
    (A : Type*) [CommRing A] [IsLocalRing A] [Algebra A' A] [IsLocalHom (algebraMap A' A)]
    (C : Type*) [CommRing C] [Algebra A' C]
    (h : IsReduced (ResidueField A' ⊗[A'] C)) :
    IsReduced (ResidueField A ⊗[A'] C) ∧ IsReduced (ResidueField A ⊗[A] (A ⊗[A'] C)) := by
  haveI : IsReduced (ResidueField A' ⊗[A'] C) := h

  haveI hgeo : IsReduced (ResidueField A ⊗[ResidueField A'] (ResidueField A' ⊗[A'] C)) :=
    Algebra.isReduced_tensorProduct_of_perfectField (ResidueField A') (ResidueField A' ⊗[A'] C)
      (ResidueField A)
  have h1 : IsReduced (ResidueField A ⊗[A'] C) := by
    let e := Algebra.TensorProduct.cancelBaseChange A' (ResidueField A') (ResidueField A)
      (ResidueField A) C
    exact isReduced_of_injective e.symm e.symm.injective
  refine ⟨h1, ?_⟩

  haveI := h1
  let e' := Algebra.TensorProduct.cancelBaseChange A' A (ResidueField A) (ResidueField A) C
  exact isReduced_of_injective e' e'.injective
