import Mathlib
import P2M.Util
import P2M.Sol.S_LocalGroupLaw_exists_localExp_of_differentiableOn_of_comm_of_assoc

set_option autoImplicit false

open Topology

theorem LocalGroupLaw.exists_localExp_of_differentiableOn_of_comm_of_assoc
    {g : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (F : (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ))
    (hF : DifferentiableOn ℂ (fun p : (Fin g → ℂ) × (Fin g → ℂ) => F p.1 p.2)
      (Metric.ball (0 : Fin g → ℂ) ρ ×ˢ Metric.ball (0 : Fin g → ℂ) ρ))
    (hzero_left : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) ρ, F 0 v = v)
    (hzero_right : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) ρ, F v 0 = v)
    (hcomm : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) ρ → w ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      F v w = F w v)
    (hassoc : ∀ u v w : Fin g → ℂ, u ∈ Metric.ball (0 : Fin g → ℂ) ρ → v ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      w ∈ Metric.ball (0 : Fin g → ℂ) ρ → F u v ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      F v w ∈ Metric.ball (0 : Fin g → ℂ) ρ → F (F u v) w = F u (F v w)) :
    ∃ (r : ℝ) (_ : 0 < r) (e : (Fin g → ℂ) → (Fin g → ℂ)),
      e 0 = 0 ∧
      DifferentiableOn ℂ e (Metric.ball (0 : Fin g → ℂ) r) ∧
      HasFDerivAt e (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 ∧
      Set.InjOn e (Metric.ball (0 : Fin g → ℂ) r) ∧
      Set.MapsTo e (Metric.ball (0 : Fin g → ℂ) r) (Metric.ball (0 : Fin g → ℂ) ρ) ∧
      (∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r → w ∈ Metric.ball (0 : Fin g → ℂ) r →
        v + w ∈ Metric.ball (0 : Fin g → ℂ) r → e (v + w) = F (e v) (e w)) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Metric.ball (0 : Fin g → ℂ) δ,
        ∃ v ∈ Metric.ball (0 : Fin g → ℂ) r, e v = x) := by p2m_exact_reverting @_root_.P2MW.S_LocalGroupLaw_exists_localExp_of_differentiableOn_of_comm_of_assoc.solution
