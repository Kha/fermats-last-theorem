import Mathlib
import P2M.Util
import P2M.Sol.S_Pencil_norm_minor_le_two_mul_sup_minor_row

theorem Pencil.norm_minor_le_two_mul_sup_minor_row {r : ℕ} (v w : Fin r → ℂ) {i₀ : Fin r}
    (hi₀ : ∀ i, ‖v i‖ ≤ ‖v i₀‖) (i j : Fin r) :
    ‖v i * w j - v j * w i‖ ≤ 2 * ⨆ l, ‖v i₀ * w l - v l * w i₀‖ := by p2m_exact_reverting @_root_.P2MW.S_Pencil_norm_minor_le_two_mul_sup_minor_row.solution
