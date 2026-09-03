import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isAffineOpen_of_finite_of_isProper_of_forall_smoothOfRelativeDimension_one
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth
attribute [-simp] AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory open AlgebraicGeometry hiding isAffine_of_isClosedImmersion_of_isAffine_of_iUnion_range_eq_univ

theorem AlgebraicGeometry.exists_isAffineOpen_of_finite_of_isProper_of_forall_smoothOfRelativeDimension_one
    (k : Type) [CommRing k] (hk : IsField k)
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    (hsep : IsSeparated f) (hqc : QuasiCompact f) (hft : LocallyOfFiniteType f)
    (hred : IsReduced X)
    (hprop : IsProper f)
    (hcomp : ∀ Y ∈ irreducibleComponents X, ∃ (C : Scheme.{0}) (i : C ⟶ X),
      IsClosedImmersion i ∧ IsIntegral C ∧ Set.range i.base = Y ∧ SmoothOfRelativeDimension 1 (i ≫ f))
    (hdim : ∀ z : X, IsClosed ({z} : Set X) ∨ closure ({z} : Set X) ∈ irreducibleComponents X)
    (hinf : ∀ C ∈ irreducibleComponents X, Set.Infinite C)
    (S : Set X) (hS : S.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ S ⊆ (U : Set X) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_of_finite_of_isProper_of_forall_smoothOfRelativeDimension_one.solution
