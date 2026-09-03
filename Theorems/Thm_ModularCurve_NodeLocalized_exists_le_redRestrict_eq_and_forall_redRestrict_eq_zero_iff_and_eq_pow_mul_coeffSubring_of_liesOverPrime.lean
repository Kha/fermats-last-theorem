import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_NodeLocalized_exists_le_redRestrict_eq_and_forall_redRestrict_eq_zero_iff_and_eq_pow_mul_coeffSubring_of_liesOverPrime
attribute [-instance] ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.qExpandAlgHomC_apply ModularCurve.evalAtJqN_X
attribute [-simp] ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve hiding exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq_level open ModularCurve.NodeLocalized hiding exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul isDiscreteValuationRing_coeffSubring

theorem ModularCurve.NodeLocalized.exists_le_redRestrict_eq_and_forall_redRestrict_eq_zero_iff_and_eq_pow_mul_coeffSubring_of_liesOverPrime
    (p : ℕ) [Fact p.Prime] (Ab : ValuationSubring (AlgebraicClosure ℚ)) (hAb : Ab.LiesOverPrime p)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (ϖb : ↥(coeffSubring Ab K))
    (hϖb : ∀ d : ↥(coeffSubring Ab K), redRestrict (IsLocalRing.residue ↥Ab) K d = 0 ↔ ∃ d', d = ϖb * d')
    (e₀ : ℕ) (ε : ↥(coeffSubring Ab K)) (hε : IsUnit ε)
    (hpε : ((p : ℕ) : ↥(coeffSubring Ab K)) = ϖb ^ e₀ * ε)
    (j₀ : IsLocalRing.ResidueField ↥Ab) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K') (_ : K ≤ K')
      (xw : ↥(coeffSubring Ab K')) (_ : redRestrict (IsLocalRing.residue ↥Ab) K' xw = j₀)
      (ϖ' : ↥(coeffSubring Ab K'))
      (_ : ∀ d : ↥(coeffSubring Ab K'), redRestrict (IsLocalRing.residue ↥Ab) K' d = 0 ↔ ∃ d', d = ϖ' * d')
      (r : ℕ) (_ : 1 ≤ r) (u : ↥(coeffSubring Ab K')) (_ : IsUnit u)
      (_ : (ϖb : AlgebraicClosure ℚ) = ((ϖ' ^ r * u : ↥(coeffSubring Ab K')) : AlgebraicClosure ℚ))
      (ε' : ↥(coeffSubring Ab K')) (_ : IsUnit ε'),
      ((p : ℕ) : ↥(coeffSubring Ab K')) = ϖ' ^ (r * e₀) * ε' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_exists_le_redRestrict_eq_and_forall_redRestrict_eq_zero_iff_and_eq_pow_mul_coeffSubring_of_liesOverPrime.solution
