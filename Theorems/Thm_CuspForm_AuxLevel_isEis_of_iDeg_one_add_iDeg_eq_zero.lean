import Definitions.Def_CohCarrier_Tower
import Definitions.Def_CuspForm_AuxLevelHeckeModule
import P2M.Util
import P2M.Sol.S_CuspForm_AuxLevel_isEis_of_iDeg_one_add_iDeg_eq_zero
attribute [-instance] CohCarrier.GammaHLower_finiteIndex Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.gamma0UnitsHom_coe Ihara.gamma0UnitsChar_apply Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply

set_option autoImplicit false

theorem CuspForm.AuxLevel.isEis_of_iDeg_one_add_iDeg_eq_zero
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N r : ℕ) [NeZero r] (hr : r.Prime) (hrN : ¬ r ∣ N)
    (h₁ : CohCarrier.LevelLE N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) 1)
    (hr' : CohCarrier.LevelLE N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) r)
    (hA : ∀ a : A, (r - 1) • a = 0 → a = 0)
    (hℓ : ℓ₀.Prime) (hℓNr : ¬ ℓ₀ ∣ N * r)
    (g h : CohCarrier.H1 N ⊤ A)
    (hgh : CohCarrier.iDeg' N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) 1 A h₁ g +
      CohCarrier.iDeg' N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) r A hr' h = 0) :
    CohCarrier.IsEis R A N ⊤ ℓ₀ g ∧ CohCarrier.IsEis R A N ⊤ ℓ₀ h := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_AuxLevel_isEis_of_iDeg_one_add_iDeg_eq_zero.solution
