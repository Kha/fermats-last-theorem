import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import P2M.Util
import P2M.Sol.S_TwoChartCech_finrank_H0_gluedLinesSections_of_sub_one_le_of_neg
set_option autoImplicit false
open LaurentPolynomial TwoChartCech

universe u

theorem TwoChartCech.finrank_H0_gluedLinesSections_of_sub_one_le_of_neg
    (k : Type u) [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (ha : Function.Injective a) (n m : ℤ)
    (hn : (s : ℤ) - 1 ≤ n) (hm : m < 0) :
    Module.finrank k ↥(gluedLinesSections k a b lam n m).H0 = (n + 1 - s).toNat := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_finrank_H0_gluedLinesSections_of_sub_one_le_of_neg.solution
