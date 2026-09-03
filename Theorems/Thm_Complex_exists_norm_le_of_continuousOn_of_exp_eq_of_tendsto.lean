import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto

set_option autoImplicit false

theorem Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
    {Λ ℓ : ℝ → ℂ} {a : ℝ} {c : ℂ} (hΛ : ContinuousOn Λ (Set.Ioi a))
    (hexp : ∀ s : ℝ, a < s → Complex.exp (Λ s) = ℓ s)
    (hlim : Filter.Tendsto ℓ (nhdsWithin a (Set.Ioi a)) (nhds c)) (hc : c ≠ 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, a < s → s < a + δ → ‖Λ s‖ ≤ C := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.solution
