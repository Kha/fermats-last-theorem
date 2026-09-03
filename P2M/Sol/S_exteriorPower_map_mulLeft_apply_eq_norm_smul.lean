import Mathlib
import Theorems.Thm_exteriorPower_map_apply_eq_det_smul
import P2M.Util
namespace P2MW.S_exteriorPower_map_mulLeft_apply_eq_norm_smul

set_option autoImplicit false

theorem solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A B) {n : ℕ} (hn : Fintype.card ι = n)
    (x : B) (w : ⋀[A]^n B) :
    exteriorPower.map n (LinearMap.mulLeft A x) w = Algebra.norm A x • w := by
  rw [exteriorPower.map_apply_eq_det_smul b hn, Algebra.norm_apply]
  rfl
