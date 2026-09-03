import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_det_heckeULin_two_eq_pow_finrank_or_eq_neg
attribute [-instance] Ihara.instGroupIharaAmalgam
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply
set_option autoImplicit false

theorem CuspForm.det_heckeULin_two_eq_pow_finrank_or_eq_neg
    (p : ℕ) [Fact p.Prime] (R : ℕ) [NeZero R] (hpR : ¬ p ∣ R) :
    haveI : NeZero (R * p) := ⟨Nat.mul_ne_zero (NeZero.ne R) (Fact.out : p.Prime).ne_zero⟩
    LinearMap.det (CuspForm.heckeULin 2 (dvd_mul_left p R) :
        CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2)
        = (p : ℂ) ^ Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 R) 2) ∨
      LinearMap.det (CuspForm.heckeULin 2 (dvd_mul_left p R) :
        CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2)
        = -(p : ℂ) ^ Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 R) 2) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_det_heckeULin_two_eq_pow_finrank_or_eq_neg.solution
