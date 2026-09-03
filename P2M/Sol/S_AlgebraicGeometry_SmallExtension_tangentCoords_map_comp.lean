import Mathlib
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_SmallExtension_tangentCoords_map_comp

set_option autoImplicit false

open TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u

theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C] (C' : Type u) [CommRing C'] [Algebra T' C'] (h : C →ₐ[T'] C')
    {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a : A) :
    tangentCoords T' V C'
        ((Algebra.TensorProduct.map
            (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h)
            (AlgHom.id (ResidueField T') (TrivSqZeroExt (ResidueField T') V)) :
          thickening T' V C →ₐ[ResidueField T'] thickening T' V C').toRingHom.comp φ) a =
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h).toLinearMap ∘ₗ tangentCoords T' V C φ a := by

  have key : ∀ e : thickening T' V C,
      tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C') V
          (vPart T' V C' ((Algebra.TensorProduct.map
            (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h)
            (AlgHom.id (ResidueField T') (TrivSqZeroExt (ResidueField T') V))) e)) =
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h).toLinearMap ∘ₗ
          tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V (vPart T' V C e) := by
    intro e
    induction e using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero, map_zero, LinearMap.comp_zero]
    | tmul c y =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      show tensorToDualHom _ _ _ ((TensorProduct.map LinearMap.id (TrivSqZeroExt.sndHom (ResidueField T') V)) (_ ⊗ₜ _)) =
        _ ∘ₗ tensorToDualHom _ _ _ ((TensorProduct.map LinearMap.id (TrivSqZeroExt.sndHom (ResidueField T') V)) (_ ⊗ₜ _))
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
      apply LinearMap.ext
      intro ξ
      rw [tensorToDualHom_tmul, LinearMap.comp_apply, tensorToDualHom_tmul, LinearMap.id_apply, LinearMap.id_apply, map_smul]
      rfl
    | add e₁ e₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, map_add, h₁, h₂, LinearMap.comp_add]
  exact key (φ a)
