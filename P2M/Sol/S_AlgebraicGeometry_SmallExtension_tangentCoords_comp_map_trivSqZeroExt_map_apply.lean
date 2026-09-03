import Mathlib
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_trivSqZeroExt_map_apply

set_option autoImplicit false

open TensorProduct IsLocalRing AlgebraicGeometry AlgebraicGeometry.SmallExtension

universe u

theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C]
    (φV : V →ₗ[ResidueField T'] V)
    {A : Type u} [CommRing A] (χ : A →+* thickening T' V C) (a : A) (ξ : Module.Dual (ResidueField T') V) :
    tangentCoords T' V C
        ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
          (TrivSqZeroExt.map (R' := ResidueField T') φV)).toRingHom.comp χ) a ξ =
      tangentCoords T' V C χ a (ξ ∘ₗ φV) := by
  simp only [tangentCoords_apply, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  generalize χ a = z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul m t =>
      simp only [vPart, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, TensorProduct.map_tmul, LinearMap.id_coe,
        tensorToDualHom_tmul, LinearMap.comp_apply]
      congr 1
      show ξ ((TrivSqZeroExt.sndHom (ResidueField T') V) (TrivSqZeroExt.map φV t)) = ξ (φV ((TrivSqZeroExt.sndHom (ResidueField T') V) t))
      simp [TrivSqZeroExt.sndHom, TrivSqZeroExt.snd_map]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
