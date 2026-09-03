import Definitions.Def_WeierstrassCurve_ModularityProps
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isResiduallyModularOfLevel_of_switch

theorem WeierstrassCurve.isResiduallyModularOfLevel_of_switch {W W' : WeierstrassCurve ℤ} {N : ℕ}
    (hmod : W'.IsModularModelOfLevel N)
    (hND : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W'.Δ → ℓ ∣ N)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → W'.IsGoodPrimeFor ℓ → ℓ ≠ 5 →
      (5 : ℤ) ∣ (W'.apOfModel ℓ - W.apOfModel ℓ)) :
    W.IsResiduallyModularOfLevel 5 N := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_of_switch.solution
