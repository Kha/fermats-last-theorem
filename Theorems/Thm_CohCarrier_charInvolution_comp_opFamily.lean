import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_CohCarrier_CharInvolution
import P2M.Util
import P2M.Sol.S_CohCarrier_charInvolution_comp_opFamily

set_option autoImplicit false

theorem CohCarrier.charInvolution_comp_opFamily
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] (g : CohCarrier.Gen M S) :
    CohCarrier.charInvolution M H 𝒪 𝒪 ∘ₗ CohCarrier.opFamily M H S 𝒪 g =
      CohCarrier.opFamily M H S 𝒪 g ∘ₗ CohCarrier.charInvolution M H 𝒪 𝒪 := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_charInvolution_comp_opFamily.solution
