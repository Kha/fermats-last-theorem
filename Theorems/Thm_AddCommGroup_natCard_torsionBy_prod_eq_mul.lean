import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_natCard_torsionBy_prod_eq_mul

set_option autoImplicit false

universe u v

theorem AddCommGroup.natCard_torsionBy_prod_eq_mul
    (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] (N : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (A × B) (N : ℤ)) =
      Nat.card (Submodule.torsionBy ℤ A (N : ℤ)) * Nat.card (Submodule.torsionBy ℤ B (N : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_natCard_torsionBy_prod_eq_mul.solution
