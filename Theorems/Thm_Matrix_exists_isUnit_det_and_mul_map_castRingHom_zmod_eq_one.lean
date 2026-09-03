import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_isUnit_det_and_mul_map_castRingHom_zmod_eq_one

set_option autoImplicit false

theorem Matrix.exists_isUnit_det_and_mul_map_castRingHom_zmod_eq_one
    {m : Type} [Fintype m] [DecidableEq m] (n : ℕ)
    (g : Matrix m m ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod n)) :
    ∃ g' : Matrix m m ℤ, IsUnit ((g'.det : ℤ) : ZMod n) ∧
      (g * g').map (Int.castRingHom (ZMod n)) = 1 ∧ (g' * g).map (Int.castRingHom (ZMod n)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_isUnit_det_and_mul_map_castRingHom_zmod_eq_one.solution
