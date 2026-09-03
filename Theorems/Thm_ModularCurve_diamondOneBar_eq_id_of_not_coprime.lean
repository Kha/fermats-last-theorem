import Mathlib
import Definitions.Def_ModularCurve_X1Diamond
import P2M.Util
import P2M.Sol.S_ModularCurve_diamondOneBar_eq_id_of_not_coprime

set_option autoImplicit false

theorem ModularCurve.diamondOneBar_eq_id_of_not_coprime
    (M : ℕ) [NeZero M] {d : ℕ} (h : ¬ Nat.Coprime d M) :
    ModularCurve.diamondOneBar M d = LinearMap.id := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diamondOneBar_eq_id_of_not_coprime.solution
