import Mathlib
import Definitions.Def_Nat_MacaulayPow
import P2M.Util
import P2M.Sol.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add

set_option autoImplicit false

theorem Nat.macaulayPow_add_add_le_macaulayPow_add_of_le_add
    (d x y u v : ℕ) (hd : 1 ≤ d) (hx : x ≤ u + v)
    (hu : Nat.macaulayPow d u + y ≤ Nat.macaulayPow d y)
    (hv : Nat.macaulayPow (d + 1) v + x ≤ Nat.macaulayPow (d + 1) x) :
    Nat.macaulayPow (d + 1) x + (x + y) ≤ Nat.macaulayPow (d + 1) (x + y) := by p2m_exact_reverting @_root_.P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.solution
