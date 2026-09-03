import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyPackage_of_counterexample

theorem FreyPackage.of_counterexample (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (p : ℕ) (pp : p.Prime) (hp5 : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p) : Nonempty FreyPackage := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_of_counterexample.solution
