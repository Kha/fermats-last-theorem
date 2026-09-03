import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf
import Theorems.Thm_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import P2M.Util
namespace P2MW.S_AlgebraicCurve_germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

theorem germToFunctionField_mem_lSpaceOn_placesOf_aux
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

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) [Nonempty (U ⊓ V : C.Opens)] (s : Γ(C, U ⊓ V)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (C.germToFunctionField (U ⊓ V)).hom s ∈
      AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c U ∩ AlgebraicCurve.placesOf c V)
        (0 : AlgebraicCurve.Divisor K C.functionField) := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  have h := germToFunctionField_mem_lSpaceOn_placesOf_aux c (U ⊓ V) s
  intro v hv
  refine h v ?_
  obtain ⟨⟨x, hxU, hx, hvx⟩, ⟨y, hyV, -, hvy⟩⟩ := hv
  have hxy : x = y := eq_of_range_stalk_eq c x y (hvx.trans hvy.symm)
  subst hxy
  exact ⟨x, ⟨hxU, hyV⟩, hx, hvx⟩
