import Definitions.Def_CohCarrier_Inst
import P2M.Util
import P2M.Sol.S_CohCarrier_opFamily_comm
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

theorem CohCarrier.opFamily_comm (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]
    (L : ℕ) [NeZero L] (H : Subgroup (ZMod L)ˣ) (g h : CohCarrier.Gen L S) :
    CohCarrier.opFamily L H S 𝒪 g * CohCarrier.opFamily L H S 𝒪 h =
      CohCarrier.opFamily L H S 𝒪 h * CohCarrier.opFamily L H S 𝒪 g := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_opFamily_comm.solution
