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
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_exists_iso_pic0_baseChange_and_descent_projections_specialFibre_twoChartModel_x1_mul
attribute [-simp] AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_iso_pic0_baseChange_and_descent_projections_specialFibre_twoChartModel_x1_mul
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

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))

    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [Algebra A (ZMod p)] [Algebra (ZMod p) k] [IsScalarTower A (ZMod p) k]
    (C₁ₚ C₂ₚ : Scheme.{0}) (c₁ₚ : C₁ₚ ⟶ Spec (CommRingCat.of (ZMod p))) (c₂ₚ : C₂ₚ ⟶ Spec (CommRingCat.of (ZMod p)))
    (i₁ₚ : C₁ₚ ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)))
    (i₂ₚ : C₂ₚ ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)))
    (g₁ : C₁ ⟶ C₁ₚ) (g₂ : C₂ ⟶ C₂ₚ)
    [IsProper c₁ₚ] [SmoothOfRelativeDimension 1 c₁ₚ] [GeometricallyIntegral c₁ₚ]
    [IsProper c₂ₚ] [SmoothOfRelativeDimension 1 c₂ₚ] [GeometricallyIntegral c₂ₚ]
    (ε₁ₚ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod p)))) c₁ₚ) (ε₂ₚ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod p)))) c₂ₚ)
    (hg₁ : IsPullback g₁ c₁ c₁ₚ (specMap (ZMod p) k)) (hg₂ : IsPullback g₂ c₂ c₂ₚ (specMap (ZMod p) k))
    (hi₁ₚ : i₁ₚ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = c₁ₚ) (hi₂ₚ : i₂ₚ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = c₂ₚ)
    (hgi₁ : g₁ ≫ i₁ₚ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (hgi₂ : g₂ ≫ i₂ₚ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (D₁ₚ : RelativePic0Designation (ZMod p) c₁ₚ) (D₂ₚ : RelativePic0Designation (ZMod p) c₂ₚ)
    (hrep₁ₚ : RepresentsRelSubPic c₁ₚ ε₁ₚ (algEquivZeroCut c₁ₚ ε₁ₚ) D₁ₚ)
    (hrep₂ₚ : RepresentsRelSubPic c₂ₚ ε₂ₚ (algEquivZeroCut c₂ₚ ε₂ₚ) D₂ₚ)
    (hrep₁ₚk : RepresentsRelSubPic (baseChange (ZMod p) c₁ₚ k) (sectionBaseChange k ε₁ₚ)
      (algEquivZeroCut (baseChange (ZMod p) c₁ₚ k) (sectionBaseChange k ε₁ₚ)) (D₁ₚ.baseChange k))
    (hrep₂ₚk : RepresentsRelSubPic (baseChange (ZMod p) c₂ₚ k) (sectionBaseChange k ε₂ₚ)
      (algEquivZeroCut (baseChange (ZMod p) c₂ₚ k) (sectionBaseChange k ε₂ₚ)) (D₂ₚ.baseChange k))
    (htie₁ : Nonempty (hrep₁ₚk.poincare.L ≅ (BaseChange.ofR c₁ₚ ε₁ₚ k
        (hrep₁ₚ.poincare.pullbackAlong ⟨pullback.fst D₁ₚ.toBase (specMap (ZMod p) k), pullback.condition⟩)).L))
    (htie₂ : Nonempty (hrep₂ₚk.poincare.L ≅ (BaseChange.ofR c₂ₚ ε₂ₚ k
        (hrep₂ₚ.poincare.pullbackAlong ⟨pullback.fst D₂ₚ.toBase (specMap (ZMod p) k), pullback.condition⟩)).L)) :
    ∃ (θ₁ : SchemeHomOver D₁.toBase (D₁ₚ.baseChange k).toBase) (θ₂ : SchemeHomOver D₂.toBase (D₂ₚ.baseChange k).toBase)
      (πₚ : pullback D.toBase (specMap A k) ⟶ pullback D.toBase (specMap A (ZMod p)))
      (ν₁ₚ : SchemeHomOver (D.baseChange (ZMod p)).toBase D₁ₚ.toBase) (ν₂ₚ : SchemeHomOver (D.baseChange (ZMod p)).toBase D₂ₚ.toBase),
      IsIso θ₁.1 ∧ IsIso θ₂.1 ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s D₁.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁.some).mul s x y) θ₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁ₚk).mul s (NeronModelInfra.schemeHomOverComp x θ₁) (NeronModelInfra.schemeHomOverComp y θ₁)) ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s D₂.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some).mul s x y) θ₂ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂ₚk).mul s (NeronModelInfra.schemeHomOverComp x θ₂) (NeronModelInfra.schemeHomOverComp y θ₂)) ∧
      πₚ ≫ pullback.fst D.toBase (specMap A (ZMod p)) = pullback.fst D.toBase (specMap A k) ∧
      πₚ ≫ pullback.snd D.toBase (specMap A (ZMod p)) = pullback.snd D.toBase (specMap A k) ≫ specMap (ZMod p) k ∧
      (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some).1 ≫ θ₁.1 ≫ pullback.fst D₁ₚ.toBase (specMap (ZMod p) k) = πₚ ≫ ν₁ₚ.1 ∧
      ν₂.1 ≫ θ₂.1 ≫ pullback.fst D₂ₚ.toBase (specMap (ZMod p) k) = πₚ ≫ ν₂ₚ.1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_exists_iso_pic0_baseChange_and_descent_projections_specialFibre_twoChartModel_x1_mul.solution
