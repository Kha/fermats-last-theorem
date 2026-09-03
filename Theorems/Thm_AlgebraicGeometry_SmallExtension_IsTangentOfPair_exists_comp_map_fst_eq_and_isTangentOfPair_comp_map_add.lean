import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_IsTangentOfPair_exists_comp_map_fst_eq_and_isTangentOfPair_comp_map_add
attribute [-simp] AlgebraicGeometry.SmallExtension.tensorToDualHom_tmul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u
theorem AlgebraicGeometry.SmallExtension.IsTangentOfPair.exists_comp_map_fst_eq_and_isTangentOfPair_comp_map_add
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u v x : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hx : x ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (w₁ w₂ : Spec (CommRingCat.of (thickening T' V C)) ⟶ Y)
    (h₁ : IsTangentOfPair I V ι C u v w₁) (h₂ : IsTangentOfPair I V ι C v x w₂) :
    ∃ W : Spec (CommRingCat.of (thickening T' (V × V) C)) ⟶ Y,
      W ≫ qY = RelTangentPoints.base (V × V) (thickeningSnd T' (V × V) C) ≫ Spec.map (CommRingCat.ofHom (residue T')) ∧
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
          (TrivSqZeroExt.map (LinearMap.fst (ResidueField T') V V))).toRingHom) ≫ W = w₁ ∧
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
          (TrivSqZeroExt.map (LinearMap.snd (ResidueField T') V V))).toRingHom) ≫ W = w₂ ∧
      IsTangentOfPair I V ι C u x
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
          (TrivSqZeroExt.map (LinearMap.fst (ResidueField T') V V + LinearMap.snd (ResidueField T') V V))).toRingHom) ≫ W) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_IsTangentOfPair_exists_comp_map_fst_eq_and_isTangentOfPair_comp_map_add.solution
