import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open CategoryTheory AlgebraicGeometry

universe u
theorem AlgebraicCurve.finite_H0_H1_structureSheaf_of_smoothProperCurve {K : Type u} [Field K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (hcurve : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      AlgebraicCurve.IsCurveOver K C.functionField)
    (hL0 : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K C.functionField)))
    (hreach : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      ∃ (γ : ℤ) (D₀ : AlgebraicCurve.Divisor K C.functionField), AlgebraicCurve.RiemannGenusReachedAt γ D₀) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.structureSheafSections c).H0 ∧ Module.Finite K (𝒱.structureSheafSections c).H1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H0
        = AlgebraicCurve.ell (0 : AlgebraicCurve.Divisor K C.functionField) ∧
      Module.finrank K (𝒱.structureSheafSections c).H1 = AlgebraicCurve.genusFF K C.functionField := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve.solution
