import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_not_isIntegral_jInt_of_dvd_discriminant_not_dvd_c4

open ModularCurve
theorem ModularCurve.not_isIntegral_jInt_of_dvd_discriminant_not_dvd_c4
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓΔ : (ℓ : ℤ) ∣ W.Δ) (hℓc₄ : ¬ (ℓ : ℤ) ∣ W.c₄) :
    ¬ _root_.IsIntegral ℤ (ModularCurve.jInt W) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_not_isIntegral_jInt_of_dvd_discriminant_not_dvd_c4.solution
