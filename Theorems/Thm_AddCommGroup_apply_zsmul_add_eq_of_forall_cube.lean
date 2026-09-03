import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_apply_zsmul_add_eq_of_forall_cube

set_option autoImplicit false

theorem AddCommGroup.apply_zsmul_add_eq_of_forall_cube
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] (Λ : M → N)
    (hΛ : ∀ x y z : M,
      Λ (x + y + z) - Λ (x + y) - Λ (x + z) - Λ (y + z) + Λ x + Λ y + Λ z = Λ 0)
    (x y : M) (n : ℤ) :
    Λ (n • x + y) =
      Λ y + n • (Λ (x + y) - Λ y) + (n * (n - 1) / 2) • (Λ (2 • x) - 2 • Λ x + Λ 0) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_apply_zsmul_add_eq_of_forall_cube.solution
