import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_index_range_iotaDeg_of_prime_sq
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

theorem CohCarrier.index_range_iotaDeg_of_prime_sq (N q : ℕ) [NeZero N] [NeZero q]
    (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq' : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
    (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2)) :
    (iotaDeg N (N * q ^ 2) ⊤ ⊤ 1 h1).range.index = q * (q + 1) ∧
    (iotaDeg N (N * q ^ 2) ⊤ ⊤ q hq').range.index = q * (q + 1) ∧
    (iotaDeg N (N * q ^ 2) ⊤ ⊤ (q ^ 2) hq2).range.index = q * (q + 1) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_index_range_iotaDeg_of_prime_sq.solution
