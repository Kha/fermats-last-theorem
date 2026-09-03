import Mathlib
import P2M.Util
import P2M.Sol.S_DeligneSerre_eq_of_eulerProduct_completedLSeries_functionalEquation

set_option autoImplicit false

open Polynomial

theorem DeligneSerre.eq_of_eulerProduct_completedLSeries_functionalEquation
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (a b : ℕ → ℂ) (ha₁ : a 1 = 1) (hb₁ : b 1 = 1)
    (hamul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hbmul : ∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n)
    (P Q : ℕ → ℂ[X])
    (hP : ∀ p : ℕ, p.Prime → (P p : PowerSeries ℂ) * PowerSeries.mk (fun k => a (p ^ k)) = 1)
    (hQ : ∀ p : ℕ, p.Prime → (Q p : PowerSeries ℂ) * PowerSeries.mk (fun k => b (p ^ k)) = 1)
    (hPQ : ∀ p : ℕ, p.Prime → p ∉ S → P p = Q p)
    (hProots : ∀ p ∈ S, ∀ z : ℂ, (P p).IsRoot z → ‖z‖ = 1)
    (hQroots : ∀ p ∈ S,
      (∀ z : ℂ, (Q p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∨
        ((Q p).natDegree ≤ 2 ∧ ‖(Q p).coeff 2‖ = 1))
    (Ma Mb : ℕ) (hMa : Ma ≠ 0) (hMb : Mb ≠ 0)
    (hMS : ∀ p : ℕ, p.Prime → p ∣ Ma * Mb → p ∈ S)
    (G : ℂ → ℂ) (σ₁ : ℝ) (hG : ∀ s : ℝ, σ₁ < s → G s ≠ 0)
    (hsum : ∀ s : ℝ, σ₁ < s → LSeriesSummable a s ∧ LSeriesSummable b s)
    (wa wb : ℂ) (hwa : wa ≠ 0) (hwb : wb ≠ 0)
    (Λa₁ Λa₂ Λa₁' Λa₂' Λb₁ Λb₂ Λb₁' Λb₂' : ℂ → ℂ)
    (hΛa₁ : Differentiable ℂ Λa₁) (hΛa₂ : Differentiable ℂ Λa₂)
    (hΛa₁' : Differentiable ℂ Λa₁') (hΛa₂' : Differentiable ℂ Λa₂')
    (hΛb₁ : Differentiable ℂ Λb₁) (hΛb₂ : Differentiable ℂ Λb₂)
    (hΛb₁' : Differentiable ℂ Λb₁') (hΛb₂' : Differentiable ℂ Λb₂')
    (hΛa : ∀ s : ℝ, σ₁ < s →
      Λa₂ s ≠ 0 ∧ Λa₂' s ≠ 0 ∧
      Λa₁ s = Λa₂ s * (((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries a s) ∧
      Λa₁' s = Λa₂' s *
        (((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries (fun m => starRingEnd ℂ (a m)) s))
    (hΛb : ∀ s : ℝ, σ₁ < s →
      Λb₂ s ≠ 0 ∧ Λb₂' s ≠ 0 ∧
      Λb₁ s = Λb₂ s * (((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries b s) ∧
      Λb₁' s = Λb₂' s *
        (((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries (fun m => starRingEnd ℂ (b m)) s))
    (hFEa₁ : ∀ s : ℂ, Λa₁ (1 - s) = wa * Λa₁' s) (hFEa₂ : ∀ s : ℂ, Λa₂ (1 - s) = Λa₂' s)
    (hFEb₁ : ∀ s : ℂ, Λb₁ (1 - s) = wb * Λb₁' s) (hFEb₂ : ∀ s : ℂ, Λb₂ (1 - s) = Λb₂' s) :
    Ma = Mb ∧ ∀ p ∈ S, P p = Q p := by p2m_exact_reverting @_root_.P2MW.S_DeligneSerre_eq_of_eulerProduct_completedLSeries_functionalEquation.solution
