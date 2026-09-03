import Mathlib
import P2M.Util
import P2M.Sol.S_deriv_deriv_comm_of_contDiffOn

set_option autoImplicit false

theorem deriv_deriv_comm_of_contDiffOn
    (F : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)) (hU : IsOpen U) (h0 : ((0 : ℝ), (0 : ℝ)) ∈ U)
    (hF : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) U) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => F s t) 0) 0
      = deriv (fun t : ℝ => deriv (fun s : ℝ => F s t) 0) 0 := by p2m_exact_reverting @_root_.P2MW.S_deriv_deriv_comm_of_contDiffOn.solution
