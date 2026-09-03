import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add_smul_of_apply_eq_add_mul_sub

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  NeronModelInfra GoodReductionJacobian

universe u
theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add_smul_of_apply_eq_add_mul_sub
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u : Spec (CommRingCat.of C) ⟶ Y) (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (r : ResidueField T') (ar : T') (har : residue T' ar = r)
    (ψ ψ' ψ'' : C →ₐ[T'] C)
    (hψ : ∀ x : C, Ideal.Quotient.mk (I.map (algebraMap T' C)) (ψ x) = Ideal.Quotient.mk (I.map (algebraMap T' C)) x)
    (hψ' : ∀ x : C, Ideal.Quotient.mk (I.map (algebraMap T' C)) (ψ' x) = Ideal.Quotient.mk (I.map (algebraMap T' C)) x)
    (hψ'' : ∀ x : C, ψ'' x = ψ x + algebraMap T' C ar * (ψ' x - x))
    (c c' : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hc : IsTangentCoordsOfPairAt I V ι C u (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ u) xk Lk ak Ue c)
    (hc' : IsTangentCoordsOfPairAt I V ι C u (Spec.map (CommRingCat.ofHom ψ'.toRingHom) ≫ u) xk Lk ak Ue c') :
    IsTangentCoordsOfPairAt I V ι C u (Spec.map (CommRingCat.ofHom ψ''.toRingHom) ≫ u) xk Lk ak Ue (c + r • c') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add_smul_of_apply_eq_add_mul_sub.solution
