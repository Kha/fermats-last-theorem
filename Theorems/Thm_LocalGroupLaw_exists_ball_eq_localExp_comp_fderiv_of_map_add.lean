import Mathlib
import P2M.Util
import P2M.Sol.S_LocalGroupLaw_exists_ball_eq_localExp_comp_fderiv_of_map_add

set_option autoImplicit false

open Topology

theorem LocalGroupLaw.exists_ball_eq_localExp_comp_fderiv_of_map_add
    {g : ℕ} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (F : (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ))

    (e : (Fin g → ℂ) → (Fin g → ℂ)) (he0 : e 0 = 0)
    (he : DifferentiableOn ℂ e (Metric.ball (0 : Fin g → ℂ) r))
    (hde : HasFDerivAt e (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0)
    (hinj : Set.InjOn e (Metric.ball (0 : Fin g → ℂ) r))
    (hmaps : Set.MapsTo e (Metric.ball (0 : Fin g → ℂ) r) (Metric.ball (0 : Fin g → ℂ) ρ))
    (hhom : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r → w ∈ Metric.ball (0 : Fin g → ℂ) r →
      v + w ∈ Metric.ball (0 : Fin g → ℂ) r → e (v + w) = F (e v) (e w))

    {s : ℝ} (hs : 0 < s) (h : (Fin g → ℂ) → (Fin g → ℂ)) (hh0 : h 0 = 0)
    (hh : DifferentiableOn ℂ h (Metric.ball (0 : Fin g → ℂ) s))
    (hhmaps : Set.MapsTo h (Metric.ball (0 : Fin g → ℂ) s) (Metric.ball (0 : Fin g → ℂ) ρ))
    (hhhom : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) s → w ∈ Metric.ball (0 : Fin g → ℂ) s →
      v + w ∈ Metric.ball (0 : Fin g → ℂ) s → h (v + w) = F (h v) (h w))
    (A : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (hA : HasFDerivAt h A 0) :
    ∃ s' : ℝ, 0 < s' ∧ s' ≤ s ∧
      ∀ v ∈ Metric.ball (0 : Fin g → ℂ) s', A v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ h v = e (A v) := by p2m_exact_reverting @_root_.P2MW.S_LocalGroupLaw_exists_ball_eq_localExp_comp_fderiv_of_map_add.solution
