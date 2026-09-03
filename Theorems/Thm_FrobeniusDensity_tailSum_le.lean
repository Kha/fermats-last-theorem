import Mathlib
import Definitions.Def_FrobeniusDensity_PrimeSums
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_tailSum_le

open NumberField
open scoped ENNReal

theorem FrobeniusDensity.tailSum_le
    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 ≤ s) :
    FrobeniusDensity.tailSum K s ≤ (Module.finrank ℚ K : ℝ≥0∞) * FrobeniusDensity.tailConst := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_tailSum_le.solution
