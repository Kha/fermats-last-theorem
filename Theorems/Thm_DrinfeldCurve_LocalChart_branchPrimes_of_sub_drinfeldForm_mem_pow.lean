import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_branchPrimes_of_sub_drinfeldForm_mem_pow

set_option autoImplicit false

theorem DrinfeldCurve.LocalChart.branchPrimes_of_sub_drinfeldForm_mem_pow
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : IsLocalRing.maximalIdeal W = Ideal.span {π})
    (hqW : (q : W) ∈ IsLocalRing.maximalIdeal W)
    (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (hc0 : c ≠ 0)
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2)) :
    let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u})
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u})

    (∀ a b : ℤ, ¬ ((q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) →
      ∃ P : Ideal S, P.IsPrime ∧ (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) ∧
        mkS (MvPowerSeries.C π) ∈ P ∧
        ∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
          mkS (MvPowerSeries.C ((a : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b : ℤ) : W) * MvPowerSeries.X 1 + h) ∈ P) ∧

    (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
      mkS (MvPowerSeries.C π) ∈ P →
        ∃ a b : ℤ, ¬ ((q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) ∧
          ∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C ((a : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b : ℤ) : W) * MvPowerSeries.X 1 + h) ∈ P) ∧

    (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →
      (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
      (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
      mkS (MvPowerSeries.C π) ∈ P₁ → mkS (MvPowerSeries.C π) ∈ P₂ →
      (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
          mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h) ∈ P₁) →
      (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
          mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h) ∈ P₂) →
      ¬ ((q : ℤ) ∣ a₁ ∧ (q : ℤ) ∣ b₁) → ¬ ((q : ℤ) ∣ a₂ ∧ (q : ℤ) ∣ b₂) →
      (P₁ = P₂ ↔ (q : ℤ) ∣ a₁ * b₂ - a₂ * b₁)) ∧

    (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
      mkS (MvPowerSeries.C π) ∈ P →
        ∀ s : S, s ∈ P → ∃ r : S, r ∉ P ∧ ∃ s' : S, r * s = mkS (MvPowerSeries.C π) * s') := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_branchPrimes_of_sub_drinfeldForm_mem_pow.solution
