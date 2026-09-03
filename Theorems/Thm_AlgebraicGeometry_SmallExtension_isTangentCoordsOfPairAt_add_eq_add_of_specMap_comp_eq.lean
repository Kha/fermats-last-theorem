import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add_eq_add_of_specMap_comp_eq
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq Algebra.PointDerivations.map_apply_coe

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  NeronModelInfra GoodReductionJacobian

universe u
theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add_eq_add_of_specMap_comp_eq
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
    (ψ₀ ψ₁ : C →ₐ[T'] C)
    (hψ₀ : ∀ c : C, Ideal.Quotient.mk (I.map (algebraMap T' C)) (ψ₀ c) = Ideal.Quotient.mk (I.map (algebraMap T' C)) c)
    (hψ₁ : ∀ c : C, Ideal.Quotient.mk (I.map (algebraMap T' C)) (ψ₁ c) = Ideal.Quotient.mk (I.map (algebraMap T' C)) c)
    (vT vT' vA₀ vA₁ : Spec (CommRingCat.of C) ⟶ Y)
    (hvT' : vT' ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hvA₁ : vA₁ ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hA₀ : vA₀ = Spec.map (CommRingCat.ofHom ψ₀.toRingHom) ≫ u)
    (hT : vT = Spec.map (CommRingCat.ofHom ψ₁.toRingHom) ≫ u)
    (hcomm : Spec.map (CommRingCat.ofHom ψ₀.toRingHom) ≫ vT' = Spec.map (CommRingCat.ofHom ψ₁.toRingHom) ≫ vA₁)
    (cs cs' b₀ b₁ : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hcs : IsTangentCoordsOfPairAt I V ι C u vT xk Lk ak Ue cs)
    (hcs' : IsTangentCoordsOfPairAt I V ι C u vT' xk Lk ak Ue cs')
    (hb₀ : IsTangentCoordsOfPairAt I V ι C u vA₀ xk Lk ak Ue b₀)
    (hb₁ : IsTangentCoordsOfPairAt I V ι C u vA₁ xk Lk ak Ue b₁) :
    b₀ + cs' = cs + b₁ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add_eq_add_of_specMap_comp_eq.solution
