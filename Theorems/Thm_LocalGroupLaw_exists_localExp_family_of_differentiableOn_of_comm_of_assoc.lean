import Mathlib
import P2M.Util
import P2M.Sol.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc

set_option autoImplicit false

open Topology

theorem LocalGroupLaw.exists_localExp_family_of_differentiableOn_of_comm_of_assoc
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (z₀ : P) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (F : P → E → E → E)
    (hF : DifferentiableOn ℂ (fun q : P × (E × E) => F q.1 q.2.1 q.2.2)
      (Metric.ball z₀ σ ×ˢ (Metric.ball (0 : E) ρ ×ˢ Metric.ball (0 : E) ρ)))
    (hzero_left : ∀ z ∈ Metric.ball z₀ σ, ∀ v ∈ Metric.ball (0 : E) ρ, F z 0 v = v)
    (hzero_right : ∀ z ∈ Metric.ball z₀ σ, ∀ v ∈ Metric.ball (0 : E) ρ, F z v 0 = v)
    (hcomm : ∀ z ∈ Metric.ball z₀ σ, ∀ v w : E, v ∈ Metric.ball (0 : E) ρ → w ∈ Metric.ball (0 : E) ρ →
      F z v w = F z w v)
    (hassoc : ∀ z ∈ Metric.ball z₀ σ, ∀ u v w : E, u ∈ Metric.ball (0 : E) ρ → v ∈ Metric.ball (0 : E) ρ →
      w ∈ Metric.ball (0 : E) ρ → F z u v ∈ Metric.ball (0 : E) ρ → F z v w ∈ Metric.ball (0 : E) ρ →
      F z (F z u v) w = F z u (F z v w)) :
    ∃ (σ' r δ : ℝ) (e ℓ : P → E → E), 0 < σ' ∧ σ' ≤ σ ∧ 0 < r ∧ 0 < δ ∧
      DifferentiableOn ℂ (fun q : P × E => e q.1 q.2) (Metric.ball z₀ σ' ×ˢ Metric.ball (0 : E) r) ∧
      DifferentiableOn ℂ (fun q : P × E => ℓ q.1 q.2) (Metric.ball z₀ σ' ×ˢ Metric.ball (0 : E) δ) ∧
      ∀ z ∈ Metric.ball z₀ σ',
        e z 0 = 0 ∧
        HasFDerivAt (e z) (ContinuousLinearMap.id ℂ E) 0 ∧
        Set.InjOn (e z) (Metric.ball (0 : E) r) ∧
        Set.MapsTo (e z) (Metric.ball (0 : E) r) (Metric.ball (0 : E) ρ) ∧
        (∀ v w : E, v ∈ Metric.ball (0 : E) r → w ∈ Metric.ball (0 : E) r → v + w ∈ Metric.ball (0 : E) r →
          e z (v + w) = F z (e z v) (e z w)) ∧
        (∀ x ∈ Metric.ball (0 : E) δ, ∃ v ∈ Metric.ball (0 : E) r, e z v = x) ∧
        (∀ v ∈ Metric.ball (0 : E) r, ℓ z (e z v) = v) ∧
        (∀ x ∈ Metric.ball (0 : E) δ, ℓ z x ∈ Metric.ball (0 : E) r ∧ e z (ℓ z x) = x) := by p2m_exact_reverting @_root_.P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.solution
