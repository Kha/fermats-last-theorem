import Mathlib.NumberTheory.Height.NumberField
import P2M.Util
import P2M.Sol.S_Height_logHeight_coeff_factor_le

theorem Height.logHeight_coeff_factor_le (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    ∃ c : ℝ, ∀ p q : Polynomial K, p ≠ 0 → p.natDegree ≤ n → q.Monic → q ∣ p →
      Height.logHeight (fun k : Fin (n + 1) => q.coeff k)
        ≤ Height.logHeight (fun k : Fin (n + 1) => p.coeff k) + c := by p2m_exact_reverting @_root_.P2MW.S_Height_logHeight_coeff_factor_le.solution
