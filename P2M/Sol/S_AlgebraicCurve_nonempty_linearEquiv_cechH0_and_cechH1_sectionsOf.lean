import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
import P2M.Util
namespace P2MW.S_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

open AlgebraicCurve in

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    (h0 : Nonempty 𝒱.U0) (h1 : Nonempty 𝒱.U1)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ D : AlgebraicCurve.Divisor K X.functionField,
      Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[K]
        ↥(AlgebraicCurve.cechH0 (AlgebraicCurve.placesOf x 𝒱.U0) (AlgebraicCurve.placesOf x 𝒱.U1) D)) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[K]
        AlgebraicCurve.cechH1 (AlgebraicCurve.placesOf x 𝒱.U0) (AlgebraicCurve.placesOf x 𝒱.U1) D) := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨D, φ, hnat, hsmul, hinj, hrange, -⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x M hM
  exact ⟨D, nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn 𝒱 x h0 h1 M D φ hnat
    (fun U _ a m => hsmul U a m) hinj hrange⟩
