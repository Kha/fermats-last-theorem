import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import P2M.Util
import P2M.Sol.S_TwoChartCech_finrank_H0_gluedLinesSections_zero_zero_le_one

set_option autoImplicit false

open TwoChartCech

universe u

theorem TwoChartCech.finrank_H0_gluedLinesSections_zero_zero_le_one
    (k : Type u) [Field k] {s : ℕ} (hs : 0 < s) (a b lam : Fin s → kˣ) :
    Module.finrank k ↥(gluedLinesSections k a b lam 0 0).H0 ≤ 1 ∧
      (Module.finrank k ↥(gluedLinesSections k a b lam 0 0).H0 = 1 ↔ ∀ i j, lam i = lam j) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_finrank_H0_gluedLinesSections_zero_zero_le_one.solution
