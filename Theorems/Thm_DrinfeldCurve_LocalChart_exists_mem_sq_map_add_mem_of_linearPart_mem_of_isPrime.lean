import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_exists_mem_sq_map_add_mem_of_linearPart_mem_of_isPrime

set_option autoImplicit false

open MvPowerSeries IsLocalRing

theorem DrinfeldCurve.LocalChart.exists_mem_sq_map_add_mem_of_linearPart_mem_of_isPrime
    (q : ℕ) [Fact q.Prime]
    (W₀ W : Type) [CommRing W₀] [IsLocalRing W₀] [CommRing W] [IsLocalRing W] (ψ : W₀ →+* W)
    (π₀ : W₀) (hπ₀ : maximalIdeal W₀ = Ideal.span {π₀})
    (hqW₀ : (q : W₀) ∈ maximalIdeal W₀) (hqW : (q : W) ∈ maximalIdeal W)
    (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀) (hu₀ : IsUnit u₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1}) ^ (q + 2))

    (Q : Ideal (MvPowerSeries (Fin 2) W)) (hQ : Q.IsPrime)
    (hQg : MvPowerSeries.map ψ (C π₀ * v₀ - f₀ * u₀) ∈ Q)

    (hQX : (X 0 : MvPowerSeries (Fin 2) W) ∉ Q ∨ (X 1 : MvPowerSeries (Fin 2) W) ∉ Q)

    (hQπ : (C (ψ π₀) : MvPowerSeries (Fin 2) W) ∈ Q)

    (a b : ℤ)
    (hab : ∃ h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ 2,
      C ((a : ℤ) : W) * X 0 + C ((b : ℤ) : W) * X 1 + h ∈ Q) :

    ∃ h₀ ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1}) ^ 2,
      MvPowerSeries.map ψ (C ((a : ℤ) : W₀) * X 0 + C ((b : ℤ) : W₀) * X 1 + h₀) ∈ Q := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_mem_sq_map_add_mem_of_linearPart_mem_of_isPrime.solution
