import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

theorem CohCarrier.heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero
    (N r : ℕ) [NeZero N] [NeZero r] (hr : r.Prime) (hrN : ¬ r ∣ N)
    (A : Type) [AddCommGroup A]

    (h₁ : CohCarrier.LevelLE N (N * r) ⊤ ⊤ 1) (hr' : CohCarrier.LevelLE N (N * r) ⊤ ⊤ r)

    (φ : CohCarrier.H1 (N * r) ⊤ A)
    (hφ₁ : CohCarrier.jDeg N (N * r) ⊤ ⊤ 1 A h₁ φ = 0)
    (hφr : CohCarrier.jDeg N (N * r) ⊤ ⊤ r A hr' φ = 0) :
    CohCarrier.heckeT (N * r) ⊤ r A (CohCarrier.heckeT (N * r) ⊤ r A φ) = φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero.solution
