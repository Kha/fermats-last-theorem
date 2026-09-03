import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

import Definitions.Def_ModularCurve_ModularUnit
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_image_range_eq_range_of_geometric_specialFibre_twoChartModel_x1_mul

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian TensorProduct

theorem ModularCurve.XOneP.image_range_eq_range_of_geometric_specialFibre_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j)) (hε : Set.range ε.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)))
    (k : Type) [Field k] [IsAlgClosed k] (ι₀ : (AlgebraicClosure (IsLocalRing.ResidueField A)) →+* k)
    {C₁ C₂ : Scheme.{0}} [IrreducibleSpace ↥C₁] [IrreducibleSpace ↥C₂]
    (i₁ : C₁ ⟶ (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))))) (i₂ : C₂ ⟶ (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))))) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))), z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (hε : ((sectionFibrePoint ε (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.base \ Set.range i₂.base)
    (hne : ¬ Set.range i₂.base ⊆ Set.range i₁.base)
    {D₁ D₂ : Scheme.{0}} (d₁ : D₁ ⟶ Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A)))) (d₂ : D₂ ⟶ Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A))))
    [GeometricallyIntegral d₁] [GeometricallyIntegral d₂]
    (j₁ : D₁ ⟶ (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))) (j₂ : D₂ ⟶ (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))) [IsClosedImmersion j₁] [IsClosedImmersion j₂]
    (hj₁ : j₁ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))) = d₁) (hj₂ : j₂ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))) = d₂)
    (hcover₀ : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))), z ∈ Set.range j₁.base ∨ z ∈ Set.range j₂.base)
    (hε₀ : ((sectionFibrePoint ε (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))).1).base (IsLocalRing.closedPoint (AlgebraicClosure (IsLocalRing.ResidueField A))) ∈ Set.range j₁.base \ Set.range j₂.base)
    (hne₀ : ¬ Set.range j₂.base ⊆ Set.range j₁.base) :
    (pullback.map (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))) (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))) (𝟙 _) (Spec.map (CommRingCat.ofHom ι₀)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])).base '' Set.range i₂.base = Set.range j₂.base := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_image_range_eq_range_of_geometric_specialFibre_twoChartModel_x1_mul.solution
