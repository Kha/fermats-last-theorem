import Mathlib
import Definitions.Def_CohCarrier_Inst
import P2M.Util
import P2M.Sol.S_CohCarrier_iDegP_jDeg_eq_finsum_diamondL

set_option autoImplicit false

theorem CohCarrier.iDegP_jDeg_eq_finsum_diamondL
    (L : ℕ) [NeZero L] (𝒪 : Type) [CommRing 𝒪]
    (H H' : Subgroup (ZMod L)ˣ) (h : CohCarrier.LevelLE L L H' H 1) (φ : CohCarrier.H1 L H 𝒪) :
    CohCarrier.iDeg' L L H' H 1 𝒪 h (CohCarrier.jDeg L L H' H 1 𝒪 h φ) =
      ∑ᶠ q : ↥H' ⧸ H.subgroupOf H', CohCarrier.diamondL L H 𝒪 ((q.out : ↥H') : (ZMod L)ˣ) φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_iDegP_jDeg_eq_finsum_diamondL.solution
