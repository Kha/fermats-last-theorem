import Definitions.Def_CohCarrier_Level
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import P2M.Util
import P2M.Sol.S_CohCarrier_subsingleton_H2_GammaH

set_option autoImplicit false

theorem CohCarrier.subsingleton_H2_GammaH {k : Type} [CommRing k] (N r : ℕ) [NeZero N] (hrN : r ∣ N)
    (hr : 4 ≤ r) (H : Subgroup (ZMod N)ˣ) (hH : ∀ u ∈ H, ZMod.castHom hrN (ZMod r) (u : ZMod N) = 1)
    (A : Rep k ↥(CohCarrier.GammaH N H)) : Subsingleton (groupCohomology A 2) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_subsingleton_H2_GammaH.solution
