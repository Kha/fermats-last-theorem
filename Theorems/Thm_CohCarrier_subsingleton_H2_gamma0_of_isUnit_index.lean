import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_subsingleton_H2_gamma0_of_isUnit_index

set_option autoImplicit false

theorem CohCarrier.subsingleton_H2_gamma0_of_isUnit_index
    {k : Type} [CommRing k] (M r : ℕ) [NeZero M] (hrM : r ∣ M) (hr : 4 ≤ r)
    (H : Subgroup (ZMod M)ˣ) (hH : ∀ u ∈ H, ZMod.castHom hrM (ZMod r) (u : ZMod M) = 1)
    (hunit : IsUnit ((H.index : ℕ) : k))
    (A : Rep k ↥(CongruenceSubgroup.Gamma0 M)) : Subsingleton (groupCohomology A 2) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_subsingleton_H2_gamma0_of_isUnit_index.solution
