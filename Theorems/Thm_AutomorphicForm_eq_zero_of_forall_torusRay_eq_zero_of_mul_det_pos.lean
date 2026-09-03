import Definitions.Def_AutomorphicForm_ArchWeightChar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_eq_zero_of_forall_torusRay_eq_zero_of_mul_det_pos

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.eq_zero_of_forall_torusRay_eq_zero_of_mul_det_pos
    (B : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (u z : ℝ → ℂ) (χ : rowIsometrySubgroup₀ ℝ → ℂ)
    (hU : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → B (!![1, t; 0, 1] * x) = u t * B x)
    (hZ : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → B (t • x) = z t * B x)
    (hK : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      B ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        χ r * B (x : Matrix (Fin 2) (Fin 2) ℝ))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h0 : ∀ y : ℝ, 0 < y → B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = 0)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < ε * x.det) :
    B x = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_eq_zero_of_forall_torusRay_eq_zero_of_mul_det_pos.solution
