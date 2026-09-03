import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_diamondRaw_comm
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

theorem CohCarrier.heckeT_diamondRaw_comm (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (σ : CongruenceSubgroup.Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0)
    {V : Type} [AddCommGroup V] (F : H1 M H V) :
    heckeT M H ℓ V (diamondRaw M H V σ F) = diamondRaw M H V σ (heckeT M H ℓ V F) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_diamondRaw_comm.solution
