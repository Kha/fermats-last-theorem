import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf
import Theorems.Thm_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import P2M.Util
namespace P2MW.S_AlgebraicCurve_germToFunctionField_mem_lSpaceOn_placesOf
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C]
    (U : C.Opens) [Nonempty (U : C.Opens)] (s : Γ(C, U)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (C.germToFunctionField U).hom s ∈
      AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c U) (0 : AlgebraicCurve.Divisor K C.functionField) := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  rintro v ⟨x, hxU, -, hvx⟩
  simp only [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
  rw [← Place.mem_iff_adicValuation_le_one]
  change (C.germToFunctionField U).hom s ∈ v.toValuationSubring.toSubring
  rw [← hvx]
  letI := C.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  haveI := AlgebraicGeometry.functionField_isScalarTower (X := C) U ⟨x, hxU⟩
  exact RingHom.mem_range.mpr ⟨algebraMap Γ(C, U) (C.presheaf.stalk x) s,
    (IsScalarTower.algebraMap_apply Γ(C, U) (C.presheaf.stalk x) C.functionField s).symm⟩
