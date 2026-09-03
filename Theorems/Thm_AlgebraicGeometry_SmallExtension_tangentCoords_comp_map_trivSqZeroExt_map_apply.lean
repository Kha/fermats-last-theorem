import Mathlib
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_trivSqZeroExt_map_apply

set_option autoImplicit false

open TensorProduct IsLocalRing AlgebraicGeometry AlgebraicGeometry.SmallExtension

universe u

theorem AlgebraicGeometry.SmallExtension.tangentCoords_comp_map_trivSqZeroExt_map_apply
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C]
    (φV : V →ₗ[ResidueField T'] V)
    {A : Type u} [CommRing A] (χ : A →+* thickening T' V C) (a : A) (ξ : Module.Dual (ResidueField T') V) :
    tangentCoords T' V C
        ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
          (TrivSqZeroExt.map (R' := ResidueField T') φV)).toRingHom.comp χ) a ξ =
      tangentCoords T' V C χ a (ξ ∘ₗ φV) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_trivSqZeroExt_map_apply.solution
