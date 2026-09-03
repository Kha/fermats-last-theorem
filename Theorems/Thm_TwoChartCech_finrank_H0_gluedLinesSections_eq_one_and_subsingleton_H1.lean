import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import P2M.Util
import P2M.Sol.S_TwoChartCech_finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1

set_option autoImplicit false

open TwoChartCech

universe u

theorem TwoChartCech.finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1
    (k : Type u) [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (ha : Function.Injective a) :
    Module.finrank k ↥(gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H0 = 1 ∧
      Subsingleton (gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H1 := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1.solution
