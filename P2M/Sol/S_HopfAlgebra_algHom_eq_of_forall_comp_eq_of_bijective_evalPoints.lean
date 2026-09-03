import Mathlib
import P2M.Util
namespace P2MW.S_HopfAlgebra_algHom_eq_of_forall_comp_eq_of_bijective_evalPoints

set_option autoImplicit false
open scoped TensorProduct

namespace Desc0
variable (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]

set_option quotPrecheck false in
local notation "F′" => ↥(IntermediateField.fixedField D)
local notation "Qb" => AlgebraicClosure ℚ

theorem main
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
        (Pi.algHom ↥(IntermediateField.fixedField D) _
          fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) =>
            (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A →ₐ[AlgebraicClosure ℚ]
          (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)))
    (u u' : A →ₐ[F′] A)
    (h : ∀ ν : A →ₐ[F′] Qb, ν.comp u = ν.comp u') :
    u = u' := by

  set L := Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A →ₐ[F′] Qb) → Qb))
        (Pi.algHom F′ _ fun ν : WithConv (A →ₐ[F′] Qb) => (WithConv.ofConv ν : A →ₐ[F′] Qb))
        (fun _ _ => Commute.all _ _) with hL
  have hinc : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[F′] Qb ⊗[F′] A) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F′ Qb).injective
  have hLinc : ∀ a : A, L (Algebra.TensorProduct.includeRight a) =
      fun ν => (WithConv.ofConv ν : A →ₐ[F′] Qb) a := by
    intro a
    simp [hL, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul]
    rfl
  apply AlgHom.ext
  intro a
  apply hinc
  apply hev.1
  rw [hLinc, hLinc]
  funext ν
  exact DFunLike.congr_fun (h (WithConv.ofConv ν)) a

end Desc0

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
    (u u' : A →ₐ[↥(IntermediateField.fixedField D)] A)
    (h : ∀ ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ, ν.comp u = ν.comp u') :
    u = u' :=
  Desc0.main D A hev u u' h
