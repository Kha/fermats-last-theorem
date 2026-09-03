import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_germToFunctionField_mem_lSpaceOn_placesOf
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
namespace AlgebraicCurve

theorem germToFunctionField_mem_lSpaceOn_placesOf
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C]
    (U : C.Opens) [Nonempty (U : C.Opens)] (s : Γ(C, U)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (C.germToFunctionField U).hom s ∈
      AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c U) (0 : AlgebraicCurve.Divisor K C.functionField) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_germToFunctionField_mem_lSpaceOn_placesOf.solution
end AlgebraicCurve
