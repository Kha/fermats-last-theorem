import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_CuspForm_exists_coe_eq_heckeT
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

theorem CuspForm.exists_coe_eq_heckeT {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeT k p ⇑f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_coe_eq_heckeT.solution
