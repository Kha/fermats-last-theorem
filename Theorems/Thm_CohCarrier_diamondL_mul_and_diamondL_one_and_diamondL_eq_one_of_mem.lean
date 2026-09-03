import Definitions.Def_CohCarrier_Inst
import P2M.Util
import P2M.Sol.S_CohCarrier_diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem CohCarrier.diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (𝒪 : Type) [CommRing 𝒪] :
    (∀ u v : (ZMod M)ˣ, CohCarrier.diamondL M H 𝒪 (u * v) =
        CohCarrier.diamondL M H 𝒪 u * CohCarrier.diamondL M H 𝒪 v) ∧
    CohCarrier.diamondL M H 𝒪 1 = 1 ∧
    (∀ u ∈ H, CohCarrier.diamondL M H 𝒪 u = 1) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem.solution
