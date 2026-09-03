import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
namespace AlgebraicCurve

theorem germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) [Nonempty (U ⊓ V : C.Opens)] (s : Γ(C, U ⊓ V)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (C.germToFunctionField (U ⊓ V)).hom s ∈
      AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c U ∩ AlgebraicCurve.placesOf c V)
        (0 : AlgebraicCurve.Divisor K C.functionField) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_germToFunctionField_inf_mem_lSpaceOn_inter_placesOf.solution
end AlgebraicCurve
