import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_contDiffOn_infty_of_differentiableOn_pi

set_option autoImplicit false

open Topology
open scoped ContDiff

theorem Complex.contDiffOn_infty_of_differentiableOn_pi {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U := by p2m_exact_reverting @_root_.P2MW.S_Complex_contDiffOn_infty_of_differentiableOn_pi.solution
