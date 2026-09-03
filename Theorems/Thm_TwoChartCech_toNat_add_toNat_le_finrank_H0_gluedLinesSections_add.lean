import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import P2M.Util
import P2M.Sol.S_TwoChartCech_toNat_add_toNat_le_finrank_H0_gluedLinesSections_add
set_option autoImplicit false
open LaurentPolynomial TwoChartCech

universe u

theorem TwoChartCech.toNat_add_toNat_le_finrank_H0_gluedLinesSections_add
    (k : Type u) [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (ha : Function.Injective a) (n m : ℤ) :
    (n + 1).toNat + (m + 1).toNat ≤ Module.finrank k ↥(gluedLinesSections k a b lam n m).H0 + s := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_toNat_add_toNat_le_finrank_H0_gluedLinesSections_add.solution
