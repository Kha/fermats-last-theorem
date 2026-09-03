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
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Spec (CommRingCat.of A)) [IsProper c] [Flat c]
    (hreg : ∀ x : C, IsRegularLocalRing (C.presheaf.stalk x))
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hUmax : ∀ W : C.Opens, SmoothOfRelativeDimension 1 (W.ι ≫ c) → W ≤ U) (hUne : (U : Set C).Nonempty)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) c) :
    Set.range ε.1.base ⊆ (U : Set C) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal.solution
