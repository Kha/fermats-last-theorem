import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_linearEquiv_structureSheafH1_cechH1
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open CategoryTheory AlgebraicGeometry

universe u
theorem AlgebraicCurve.exists_linearEquiv_structureSheafH1_cechH1 {K : Type u} [Field K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (h0 : Nonempty 𝒱.U0) (h1 : Nonempty 𝒱.U1) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (∀ [Nonempty (𝒱.U0 ⊓ 𝒱.U1 : C.Opens)] (s : (𝒱.cover c).A01),
        (C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom s ∈
          AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c 𝒱.U0 ∩ AlgebraicCurve.placesOf c 𝒱.U1)
            (0 : AlgebraicCurve.Divisor K C.functionField)) ∧
      ∃ e : (𝒱.structureSheafSections c).H1 ≃ₗ[K]
          AlgebraicCurve.cechH1 (AlgebraicCurve.placesOf c 𝒱.U0) (AlgebraicCurve.placesOf c 𝒱.U1)
            (0 : AlgebraicCurve.Divisor K C.functionField),
        ∀ [Nonempty (𝒱.U0 ⊓ 𝒱.U1 : C.Opens)] (s : (𝒱.cover c).A01)
          (hs : (C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom s ∈
            AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c 𝒱.U0 ∩ AlgebraicCurve.placesOf c 𝒱.U1)
              (0 : AlgebraicCurve.Divisor K C.functionField)),
          e (Submodule.Quotient.mk s) =
            Submodule.Quotient.mk ⟨(C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom s, hs⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_linearEquiv_structureSheafH1_cechH1.solution
