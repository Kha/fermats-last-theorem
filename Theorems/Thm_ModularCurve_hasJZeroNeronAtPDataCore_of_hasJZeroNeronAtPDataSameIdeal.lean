import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronAtPDataCore
import P2M.Util
import P2M.Sol.S_ModularCurve_hasJZeroNeronAtPDataCore_of_hasJZeroNeronAtPDataSameIdeal

open ModularCurve

theorem ModularCurve.hasJZeroNeronAtPDataCore_of_hasJZeroNeronAtPDataSameIdeal (N q : ℕ) [NeZero N] [Fact q.Prime]
    (hqN : ¬ q ∣ N) (h : HasJZeroNeronAtPDataSameIdeal N q hqN) : HasJZeroNeronAtPDataCore N q hqN := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasJZeroNeronAtPDataCore_of_hasJZeroNeronAtPDataSameIdeal.solution
