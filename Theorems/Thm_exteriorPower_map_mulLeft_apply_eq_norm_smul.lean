import Mathlib
import P2M.Util
import P2M.Sol.S_exteriorPower_map_mulLeft_apply_eq_norm_smul

set_option autoImplicit false

theorem exteriorPower.map_mulLeft_apply_eq_norm_smul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A B) {n : ℕ} (hn : Fintype.card ι = n)
    (x : B) (w : ⋀[A]^n B) :
    exteriorPower.map n (LinearMap.mulLeft A x) w = Algebra.norm A x • w := by p2m_exact_reverting @_root_.P2MW.S_exteriorPower_map_mulLeft_apply_eq_norm_smul.solution
