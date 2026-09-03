import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Defs
import P2M.Util
import P2M.Sol.S_CuspForm_nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply

set_option autoImplicit false

theorem CuspForm.nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (hSfin : S.Finite) :
    Nonempty (Module.Basis (Fin 1)
      ↥(Algebra.adjoin ℂ {T : Module.End ℂ (CuspForm (CohCarrier.GammaH M H) 2) |
          (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
          (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ T = CuspForm.heckeULinH 2 q) ∨
          (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)})
      (CuspForm (CohCarrier.GammaH M H) 2)) ∧
    ∀ χ : ↥(Algebra.adjoin ℂ {T : Module.End ℂ (CuspForm (CohCarrier.GammaH M H) 2) |
          (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
          (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ T = CuspForm.heckeULinH 2 q) ∨
          (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)}) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ {T : Module.End ℂ (CuspForm (CohCarrier.GammaH M H) 2) |
          (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
          (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ T = CuspForm.heckeULinH 2 q) ∨
          (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)}),
        Module.End.eigenspace (a : Module.End ℂ (CuspForm (CohCarrier.GammaH M H) 2)) (χ a)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one.solution
