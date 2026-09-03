import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import P2M.Util
import P2M.Sol.S_CuspForm_IsPrimitiveForm_heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level
attribute [-instance] Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.PeterssonCoset.mapGL_apply

set_option autoImplicit false

theorem CuspForm.IsPrimitiveForm.heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level
    {M : ℕ} [NeZero M] {N : ℕ} [NeZero N] (hMN : M ∣ N)
    {χ : DirichletCharacter ℂ M} {G : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hG : CuspForm.IsPrimitiveForm χ G)
    (S : Finset ℕ) (v : CuspForm (CongruenceSubgroup.Gamma1 N) 2) (hv0 : v ≠ 0)
    (t u δ : ℕ → ℂ)
    (hvT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), CuspForm.heckeTLinOne 2 hℓ hℓN v = t ℓ • v)
    (hvD : ∀ d : ℕ, Nat.Coprime d N → CuspForm.diamondLinOne N 2 d v = δ d • v)
    (hvU : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → ∀ n : ℕ,
      ModularFormClass.qCoeff v (ℓ * n) = u ℓ * ModularFormClass.qCoeff v n)
    (ht : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → t ℓ = ModularFormClass.qCoeff G ℓ)
    (hδ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → δ ℓ = χ (ℓ : ZMod M))
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ N) :
    u q = ModularFormClass.qCoeff G q := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsPrimitiveForm_heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level.solution
