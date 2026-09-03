import Mathlib
import P2M.Util
import P2M.Sol.S_Pencil_norm_dotProduct_mul_sup_le

theorem Pencil.norm_dotProduct_mul_sup_le {r : ℕ} (a v w : Fin r → ℂ) (hav : ∑ i, a i * v i = 0) :
    ‖∑ i, a i * w i‖ * (⨆ i, ‖v i‖)
      ≤ (∑ i, ‖a i‖) * ⨆ p : Fin r × Fin r, ‖v p.1 * w p.2 - v p.2 * w p.1‖ := by p2m_exact_reverting @_root_.P2MW.S_Pencil_norm_dotProduct_mul_sup_le.solution
