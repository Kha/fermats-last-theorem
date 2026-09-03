import Mathlib
import Definitions.Def_Nat_MacaulayPow
import P2M.Util
import P2M.Sol.S_Nat_macaulayPow_lt_macaulayPow_of_lt

set_option autoImplicit false

theorem Nat.macaulayPow_lt_macaulayPow_of_lt {d : ℕ} (hd : 1 ≤ d) {a b : ℕ} (h : a < b) :
    Nat.macaulayPow d a < Nat.macaulayPow d b := by p2m_exact_reverting @_root_.P2MW.S_Nat_macaulayPow_lt_macaulayPow_of_lt.solution
