import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import P2M.Util
import P2M.Sol.S_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    (∀ (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓ' : ℓ'.Prime) (hℓ'M : ¬ ℓ' ∣ M)
        (f : CuspForm (CohCarrier.GammaH M H) k),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
      CuspForm.heckeTLinH k hℓ hℓM (CuspForm.heckeTLinH k hℓ' hℓ'M f) =
        CuspForm.heckeTLinH k hℓ' hℓ'M (CuspForm.heckeTLinH k hℓ hℓM f)) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (q : ℕ), q.Prime → q ∣ M →
        ∀ f : CuspForm (CohCarrier.GammaH M H) k,
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CuspForm.heckeTLinH k hℓ hℓM (CuspForm.heckeULinH k q f) =
        CuspForm.heckeULinH k q (CuspForm.heckeTLinH k hℓ hℓM f)) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CuspForm.heckeTLinH k hℓ hℓM (CuspForm.diamondLinH k d f) =
        CuspForm.diamondLinH k d (CuspForm.heckeTLinH k hℓ hℓM f)) ∧
    (∀ (q : ℕ), q.Prime → q ∣ M → ∀ (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k),
      CuspForm.heckeULinH k q (CuspForm.diamondLinH k d f) =
        CuspForm.diamondLinH k d (CuspForm.heckeULinH k q f)) ∧
    (∀ (d d' : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k),
      CuspForm.diamondLinH k d (CuspForm.diamondLinH k d' f) =
        CuspForm.diamondLinH k d' (CuspForm.diamondLinH k d f)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm.solution
