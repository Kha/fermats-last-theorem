import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_det_map_eq_of_isUnit_of_ne

set_option autoImplicit false

theorem Matrix.exists_det_map_eq_of_isUnit_of_ne
    (ℓ q : ℕ) [Fact ℓ.Prime] [Fact q.Prime] (hℓq : ℓ ≠ q) (u : (ZMod ℓ)ˣ) (v : (ZMod q)ˣ) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det ∧
      ((g.det : ℤ) : ZMod ℓ) = (u : ZMod ℓ) ∧ ((g.det : ℤ) : ZMod q) = (v : ZMod q) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_det_map_eq_of_isUnit_of_ne.solution
