import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace
attribute [-instance] Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply

set_option autoImplicit false

theorem CuspForm.IsNewform.maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace
    (N : ℕ) [NeZero N] (S : Finset ℕ) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform) :

    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (ν : ℂ),
      Module.End.maxGenEigenspace
          (CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ hℓN) ν ≤
        Module.End.eigenspace (CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ hℓN) ν) ∧

    ∃ v : ℕ → CuspForm (CohCarrier.GammaH N ⊤) 2,
      (∀ d : ℕ, d ∣ N / Mg → ∀ τ : UpperHalfPlane, v d τ = g (ModularForm.heckeDiagMatrix d • τ)) ∧
      LinearIndependent ℂ (fun d : ↥(Nat.divisors (N / Mg)) => v (d : ℕ)) ∧
      Submodule.span ℂ (Set.range fun d : ↥(Nat.divisors (N / Mg)) => v (d : ℕ)) =
        ⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S), Module.End.eigenspace
          (CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ (fun h => hℓS (hNS ℓ hℓ h)))
          (ModularFormClass.qCoeff g ℓ) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (d : ℕ), d ∣ N / Mg →
        (q ∣ d → CuspForm.heckeULinH 2 q (v d) = v (d / q)) ∧
        (¬ q ∣ d → q ∣ Mg → CuspForm.heckeULinH 2 q (v d) = ModularFormClass.qCoeff g q • v d) ∧
        (¬ q ∣ d → ¬ q ∣ Mg → CuspForm.heckeULinH 2 q (v d) =
          ModularFormClass.qCoeff g q • v d - (q : ℂ) • v (d * q))) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace.solution
