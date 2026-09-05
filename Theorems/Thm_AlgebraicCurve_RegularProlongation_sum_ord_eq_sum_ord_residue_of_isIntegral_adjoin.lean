module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_RegularProlongation
public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin

@[expose] public section
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hfi : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F))
    (hf : R.residue f ≠ 0)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (Dbar : Divisor (IsLocalRing.ResidueField A) Fbar)
    (hDbar : ∀ Q, Dbar Q = Q.ord (R.residue f))
    (TP : Finset (Place L F))
    (hTP : ∀ P, P ∈ TP ↔ (D P ≠ 0 ∧
      ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits))
    (TQ : Finset (Place (IsLocalRing.ResidueField A) Fbar))
    (hTQ : ∀ Q, Q ∈ TQ ↔ (Dbar Q ≠ 0 ∧ R.residue x ∈ Q.toValuationSubring)) :
    ∑ P ∈ TP, D P = ∑ Q ∈ TQ, Dbar Q := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin.solution
