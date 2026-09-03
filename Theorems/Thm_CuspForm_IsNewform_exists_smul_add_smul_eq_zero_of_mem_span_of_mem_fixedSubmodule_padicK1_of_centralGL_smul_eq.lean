import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_exists_smul_add_smul_eq_zero_of_mem_span_of_mem_fixedSubmodule_padicK1_of_centralGL_smul_eq
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AutomorphicForm.rightTranslationEmbed_smul_apply FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply

set_option autoImplicit false

theorem
CuspForm.IsNewform.exists_smul_add_smul_eq_zero_of_mem_span_of_mem_fixedSubmodule_padicK1_of_centralGL_smul_eq
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (y₁ y₂ : LocalNewvector.AdelicSpan Φ)
    (hy₁ : y₁ ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hy₂ : y₂ ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hfix₁ : y₁ ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q (M.factorization q))
      (LocalNewvector.AdelicSpan Φ))
    (hfix₂ : y₂ ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q (M.factorization q))
      (LocalNewvector.AdelicSpan Φ))
    (hcent₁ : ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • y₁ = y₁)
    (hcent₂ : ∀ z : ℚ_[q]ˣ, LocalNewvector.centralGL q z • y₂ = y₂) :
    ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • y₁ + c₂ • y₂ = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_exists_smul_add_smul_eq_zero_of_mem_span_of_mem_fixedSubmodule_padicK1_of_centralGL_smul_eq.solution
