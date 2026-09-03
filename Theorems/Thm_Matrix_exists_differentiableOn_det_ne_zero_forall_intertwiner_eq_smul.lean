import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul

set_option autoImplicit false

open Topology

theorem Matrix.exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul
    {X : Type} {n : ℕ} (ι' : X → Matrix (Fin n) (Fin n) ℂ)
    (hspan : Submodule.span ℂ (Set.range ι') = ⊤)
    (z₀ : ℂ) {ε : ℝ} (hε : 0 < ε) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ∀ (x : X) (i j : Fin n), DifferentiableOn ℂ (fun z : ℂ => ρ z x i j) (Metric.ball z₀ ε))
    (hM : ∀ z ∈ Metric.ball z₀ ε, ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det ≠ 0 ∧ ∀ x : X, M * ι' x = ρ z x * M) :
    ∃ (ε' : ℝ) (N : ℂ → Matrix (Fin n) (Fin n) ℂ), 0 < ε' ∧ ε' ≤ ε ∧
      (∀ i j : Fin n, DifferentiableOn ℂ (fun z : ℂ => N z i j) (Metric.ball z₀ ε')) ∧
      ∀ z ∈ Metric.ball z₀ ε',
        (N z).det ≠ 0 ∧ (∀ x : X, N z * ι' x = ρ z x * N z) ∧
        ∀ M : Matrix (Fin n) (Fin n) ℂ, (∀ x : X, M * ι' x = ρ z x * M) → ∃ c : ℂ, M = c • N z := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul.solution
