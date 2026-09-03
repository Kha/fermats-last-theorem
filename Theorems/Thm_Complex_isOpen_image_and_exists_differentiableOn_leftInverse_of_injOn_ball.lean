import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball

set_option autoImplicit false

open Topology

theorem Complex.isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball
    (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ ε)) (hinj : Set.InjOn f (Metric.ball z₀ ε)) :
    IsOpen (f '' Metric.ball z₀ ε) ∧
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (f '' Metric.ball z₀ ε) ∧
      (∀ z ∈ Metric.ball z₀ ε, g (f z) = z) ∧
      (∀ w ∈ f '' Metric.ball z₀ ε, g w ∈ Metric.ball z₀ ε ∧ f (g w) = w) := by p2m_exact_reverting @_root_.P2MW.S_Complex_isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball.solution
