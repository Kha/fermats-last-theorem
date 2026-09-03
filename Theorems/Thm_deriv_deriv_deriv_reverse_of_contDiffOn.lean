import Mathlib
import P2M.Util
import P2M.Sol.S_deriv_deriv_deriv_reverse_of_contDiffOn

set_option autoImplicit false

theorem deriv_deriv_deriv_reverse_of_contDiffOn
    (G : ℝ → ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ × ℝ)) (hU : IsOpen U) (h0 : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ U)
    (hG : ContDiffOn ℝ 3 (fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2) U) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => deriv (fun u : ℝ => G s t u) 0) 0) 0
      = deriv (fun u : ℝ => deriv (fun t : ℝ => deriv (fun s : ℝ => G s t u) 0) 0) 0 := by p2m_exact_reverting @_root_.P2MW.S_deriv_deriv_deriv_reverse_of_contDiffOn.solution
