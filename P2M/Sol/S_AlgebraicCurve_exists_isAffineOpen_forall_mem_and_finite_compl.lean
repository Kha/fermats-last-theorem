import Mathlib
import Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset_of_field
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import P2M.Util
namespace P2MW.S_AlgebraicCurve_exists_isAffineOpen_forall_mem_and_finite_compl
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth
attribute [-simp] AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (F : Finset C) :
    ∃ U : C.Opens, IsAffineOpen U ∧ (∀ x ∈ F, x ∈ U) ∧ ((U : Set C)ᶜ).Finite := by
  classical
  obtain ⟨U, hU, hF⟩ :=
    AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset_of_field c (insert (genericPoint C) F)
  exact ⟨U, hU, fun x hx => hF x (Finset.mem_insert_of_mem hx),
    AlgebraicCurve.finite_compl_of_isOpen c U ⟨genericPoint C, hF _ (Finset.mem_insert_self _ _)⟩⟩
