import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_CuspForm_exists_coe_eq_heckeU
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

theorem CuspForm.exists_coe_eq_heckeU {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hpN : p ∣ N) : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeU k p ⇑f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_coe_eq_heckeU.solution
