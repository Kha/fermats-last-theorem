import Mathlib
import P2M.Util
import P2M.Sol.S_exteriorPower_map_apply_eq_det_smul

set_option autoImplicit false

theorem exteriorPower.map_apply_eq_det_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {ι : Type*} [Fintype ι] (b : Module.Basis ι A M) {n : ℕ} (hn : Fintype.card ι = n)
    (f : M →ₗ[A] M) (x : ⋀[A]^n M) :
    exteriorPower.map n f x = LinearMap.det f • x := by p2m_exact_reverting @_root_.P2MW.S_exteriorPower_map_apply_eq_det_smul.solution
