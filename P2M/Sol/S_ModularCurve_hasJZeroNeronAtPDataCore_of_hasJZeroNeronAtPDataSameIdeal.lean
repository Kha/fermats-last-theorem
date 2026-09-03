import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronAtPDataCore
import P2M.Util
namespace P2MW.S_ModularCurve_hasJZeroNeronAtPDataCore_of_hasJZeroNeronAtPDataSameIdeal

open ModularCurve

theorem solution (N q : ℕ) [NeZero N] [Fact q.Prime]
    (hqN : ¬ q ∣ N) (h : HasJZeroNeronAtPDataSameIdeal N q hqN) : HasJZeroNeronAtPDataCore N q hqN := by
  exact fun A hA => (h A hA).map JZeroNeronAtPDataSameIdeal.toCore
