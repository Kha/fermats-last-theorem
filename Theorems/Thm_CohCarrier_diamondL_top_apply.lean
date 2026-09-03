import Mathlib
import Definitions.Def_CohCarrier_Inst
import P2M.Util
import P2M.Sol.S_CohCarrier_diamondL_top_apply

set_option autoImplicit false

open scoped MatrixGroups
open CongruenceSubgroup

theorem CohCarrier.diamondL_top_apply (M : ℕ) [NeZero M] (𝒪 : Type) [CommRing 𝒪]
    (d : (ZMod M)ˣ) (φ : CohCarrier.H1 M ⊤ 𝒪) :
    CohCarrier.diamondL M ⊤ 𝒪 d φ = φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_diamondL_top_apply.solution
