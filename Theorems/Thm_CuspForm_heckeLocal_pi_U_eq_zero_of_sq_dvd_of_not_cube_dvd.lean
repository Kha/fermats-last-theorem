import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
import P2M.Sol.S_CuspForm_heckeLocal_pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CuspForm.coe_heckeULowerLin_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false

open IsLocalRing

theorem CuspForm.heckeLocal.pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd
    (N : ℕ) [NeZero N] (S₀ : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ' : CuspForm.heckeAlgebra N 2 S₀ →+* ResidueField 𝒪)
    (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS₀ : q ∉ S₀) (hsq : q ^ 2 ∣ N) (hcube : ¬ q ^ 3 ∣ N)
    (hq𝒪 : IsUnit (q : 𝒪))
    (hθ' : θ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) = 0) :
    CuspForm.heckeLocal.π N S₀ 𝒪 θ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeLocal_pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd.solution
