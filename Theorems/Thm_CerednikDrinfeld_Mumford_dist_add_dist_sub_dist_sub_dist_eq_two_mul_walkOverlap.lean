import Mathlib
import Definitions.Def_CerednikDrinfeld_WalkOverlap
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_dist_add_dist_sub_dist_sub_dist_eq_two_mul_walkOverlap

set_option autoImplicit false

theorem CerednikDrinfeld.Mumford.dist_add_dist_sub_dist_sub_dist_eq_two_mul_walkOverlap
    {V : Type} [DecidableEq V] (T : SimpleGraph V) (hT : T.IsTree)
    {Z Z₀ X Y : V} (P : T.Walk Z Z₀) (Q : T.Walk X Y) :
    (T.dist Z Y : ℤ) + T.dist Z₀ X - T.dist Z X - T.dist Z₀ Y = 2 * CerednikDrinfeld.Mumford.walkOverlap P Q := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_dist_add_dist_sub_dist_sub_dist_eq_two_mul_walkOverlap.solution
