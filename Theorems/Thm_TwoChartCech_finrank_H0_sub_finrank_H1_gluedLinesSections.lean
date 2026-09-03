import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import P2M.Util
import P2M.Sol.S_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections

set_option autoImplicit false

open TwoChartCech

universe u

theorem TwoChartCech.finrank_H0_sub_finrank_H1_gluedLinesSections
    (k : Type u) [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (ha : Function.Injective a) (n m : ℤ) :
    Module.Finite k ↥(gluedLinesSections k a b lam n m).H0 ∧
      Module.Finite k (gluedLinesSections k a b lam n m).H1 ∧
      (Module.finrank k ↥(gluedLinesSections k a b lam n m).H0 : ℤ)
        - Module.finrank k (gluedLinesSections k a b lam n m).H1 = n + m + 2 - s := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections.solution
