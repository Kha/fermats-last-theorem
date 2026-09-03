import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_exists_orientedCrossingChart_valuationSubring_of_chart_twoChartModel_x1_mul

set_option autoImplicit false

open MvPolynomial CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_orientedCrossingChart_valuationSubring_of_chart_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)

    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom πk))

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : A →+* O)
    (ι : O →+* ↥Pl) (hι : ι.comp ρO = ρ) (hιinj : Function.Injective ι)
    (hιloc : ∀ o : O, ι o ∈ IsLocalRing.maximalIdeal ↥Pl ↔ o ∈ IsLocalRing.maximalIdeal O)
    (hιsurj : Function.Surjective (fun o : O => πk (ι o)))
    (hιfix : ∀ τ : ↥(Pl.decompositionSubgroup ℚ), τ ∈ Pl.inertiaSubgroup ℚ →
      (∀ l : L, (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ o : O, τ • (ι o) = ι o)

    (bcO : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbcO₁ : bcO ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbcO₂ : bcO ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (πk.comp ι)))

    (ν : ↥(pullback i₁.1 i₂.1))
    (e : ℕ) (he : 1 ≤ e) (U₀ : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).Opens)
    (hxU₀ : (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bcO).base ν ∈ U₀)
    (f₀ : (U₀ : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme ((ρO ϖ) ^ e))
    (hover₀ : f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O ((ρO ϖ) ^ e)))) = U₀.ι ≫ pullback.snd _ _)
    (hfib₀ : (∀ y : ↥(U₀ : Scheme.{0}),
            (CrossingQuotient.U ((ρO ϖ) ^ e) ∈ (f₀.base y).asIdeal ∧ CrossingQuotient.V ((ρO ϖ) ^ e) ∈ (f₀.base y).asIdeal) ↔
            U₀.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bcO).base ν))
    (hpt₀ : (∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bcO).base ν →
            (f₀.stalkMap y).hom.Flat ∧
            Ideal.map (f₀.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f₀.residueFieldMap y)))
    (het₀ : (∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bcO).base ν →
            ∃ V : (U₀ : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f₀)))
    (hor₁ : (∀ y : ↥(U₀ : Scheme.{0}), CrossingQuotient.V ((ρO ϖ) ^ e) ∈ (f₀.base y).asIdeal → U₀.ι.base y ∈ Set.range (i₁.1 ≫ bcO).base))
    (hor₂ : (∀ y : ↥(U₀ : Scheme.{0}), CrossingQuotient.U ((ρO ϖ) ^ e) ∈ (f₀.base y).asIdeal → U₀.ι.base y ∈ Set.range (i₂.1 ≫ bcO).base))
    (hor₃ : (∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y ∈ Set.range (i₁.1 ≫ bcO).base → CrossingQuotient.V ((ρO ϖ) ^ e) ∈ (f₀.base y).asIdeal))
    (hor₄ : (∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y ∈ Set.range (i₂.1 ≫ bcO).base → CrossingQuotient.U ((ρO ϖ) ^ e) ∈ (f₀.base y).asIdeal))
    :
      ∃ (U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).Opens)
        (_ : (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν ∈ U)
        (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme ((ρ ϖ) ^ e)),

        f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl ((ρ ϖ) ^ e)))) =
            U.ι ≫ pullback.snd _ _ ∧

        (∀ y : ↥(U : Scheme.{0}),
            (CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal ∧
              CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal) ↔
            U.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν →
            (f.stalkMap y).hom.Flat ∧
            Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f.residueFieldMap y)) ∧

        (∃ W : (U : Scheme.{0}).Opens,
          (∃ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν ∧ y ∈ W) ∧
          AlgebraicGeometry.Etale (W.ι ≫ f)) ∧

        (∀ (τ : ↥(Pl.decompositionSubgroup ℚ)), τ ∈ Pl.inertiaSubgroup ℚ →
          (∀ l : L, (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
          ∀ (x' y' : ↥Pl) (hxy : x' * y' = algebraMap ↥Pl ↥Pl ((ρ ϖ) ^ e))
            (hxy' : (MulSemiringAction.toRingHom _ (↥Pl) τ) x' * (MulSemiringAction.toRingHom _ (↥Pl) τ) y' =
              algebraMap ↥Pl ↥Pl ((ρ ϖ) ^ e))
            (sU sU' : Spec (CommRingCat.of ↥Pl) ⟶ (U : Scheme.{0})),
            sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ → sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
            sU' ≫ U.ι ≫ pullback.fst _ _ =
              Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom _ (↥Pl) τ)) ≫ sU ≫ U.ι ≫ pullback.fst _ _ →
            sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := (ρ ϖ) ^ e) x' y' hxy).toRingHom) →
            sU' ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := (ρ ϖ) ^ e)
              ((MulSemiringAction.toRingHom _ (↥Pl) τ) x') ((MulSemiringAction.toRingHom _ (↥Pl) τ) y') hxy').toRingHom)) ∧

        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (i₁.1 ≫ bc).base) ∧
        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (i₂.1 ≫ bc).base) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (i₁.1 ≫ bc).base →
            CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal) ∧
        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (i₂.1 ≫ bc).base →
            CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_exists_orientedCrossingChart_valuationSubring_of_chart_twoChartModel_x1_mul.solution
