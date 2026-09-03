import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import P2M.Util
import P2M.Sol.S_CohCarrier_index_comap_unitsMap

set_option autoImplicit false

theorem CohCarrier.index_comap_unitsMap
    {M M' : ℕ} [NeZero M'] (hMM' : M ∣ M') (H₀ : Subgroup (ZMod M)ˣ) :
    (H₀.comap (ZMod.unitsMap hMM')).index = H₀.index := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_index_comap_unitsMap.solution
