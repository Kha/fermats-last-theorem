import Mathlib
import P2M.Util
import P2M.Sol.S_exteriorPower_iotaMulti_comp_eq_det_smul

set_option autoImplicit false

theorem exteriorPower.iotaMulti_comp_eq_det_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {n : ℕ} (b : Module.Basis (Fin n) A M) (f : M →ₗ[A] M) (m : Fin n → M) :
    exteriorPower.ιMulti A n (f ∘ m) = LinearMap.det f • exteriorPower.ιMulti A n m := by p2m_exact_reverting @_root_.P2MW.S_exteriorPower_iotaMulti_comp_eq_det_smul.solution
