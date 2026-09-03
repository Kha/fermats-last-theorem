import Mathlib
import Definitions.Def_TateCurve_QSeries
import Definitions.Def_TateCurve_TateParameter
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_tateParameter_of_prime_dvd_discr

open scoped NNReal

theorem WeierstrassCurve.exists_tateParameter_of_prime_dvd_discr (W : WeierstrassCurve ℤ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hΔ : W.Δ ≠ 0) (hdvd : (ℓ : ℤ) ∣ W.Δ) (hndvd : ¬ (ℓ : ℤ) ∣ W.c₄) :
    ∃ qT : ℚ_[ℓ], qT ≠ 0 ∧ ‖qT‖₊ < 1 ∧
      (TateCurve.curve qT).c₄ ^ 3
        = (((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) : ℚ_[ℓ])
            * (TateCurve.curve qT).Δ ∧
      ‖qT‖₊ = ((ℓ : ℝ≥0) ^ padicValInt ℓ W.Δ)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_tateParameter_of_prime_dvd_discr.solution
