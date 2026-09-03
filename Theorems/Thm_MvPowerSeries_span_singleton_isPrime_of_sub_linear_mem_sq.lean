import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq

set_option autoImplicit false

universe u

open MvPowerSeries

theorem MvPowerSeries.span_singleton_isPrime_of_sub_linear_mem_sq
    {κ : Type u} [Field κ] (a b : κ) (hab : a ≠ 0 ∨ b ≠ 0)
    (ℓ : MvPowerSeries (Fin 2) κ)
    (hℓ : ℓ - (C a * X 0 + C b * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2) :
    (Ideal.span {ℓ}).IsPrime ∧
    ((X 0 : MvPowerSeries (Fin 2) κ) ∉ Ideal.span {ℓ} ∨ (X 1 : MvPowerSeries (Fin 2) κ) ∉ Ideal.span {ℓ}) ∧
    (∀ P : Ideal (MvPowerSeries (Fin 2) κ), P.IsPrime → ℓ ∈ P →
      ((X 0 : MvPowerSeries (Fin 2) κ) ∉ P ∨ (X 1 : MvPowerSeries (Fin 2) κ) ∉ P) → P = Ideal.span {ℓ}) ∧
    (∀ (a' b' : κ) (h' : MvPowerSeries (Fin 2) κ),
      h' ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 →
      C a' * X 0 + C b' * X 1 + h' ∈ Ideal.span {ℓ} → a * b' - a' * b = 0) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq.solution
