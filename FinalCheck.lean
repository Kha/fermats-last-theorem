import Theorems.Thm_fermat_last_theorem
/-- info: 'fermat_last_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fermat_last_theorem

theorem flt_pinned (n : ℕ) (hn : 3 ≤ n) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ n + b ^ n ≠ c ^ n := fermat_last_theorem n hn a b c ha hb hc
theorem flt_mathlib : FermatLastTheorem := fun n hn a b c ha hb hc => fermat_last_theorem n hn a b c (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc)
#print axioms flt_mathlib
