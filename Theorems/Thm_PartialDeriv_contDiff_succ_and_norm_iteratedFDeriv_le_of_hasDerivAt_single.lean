import Mathlib
import P2M.Util
import P2M.Sol.S_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single

set_option autoImplicit false

theorem PartialDeriv.contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single
    (n m : ℕ) (f : (Fin n → ℝ) → ℂ) (g : Fin n → (Fin n → ℝ) → ℂ)
    (hg : ∀ j, ContDiff ℝ m (g j))
    (hfg : ∀ (t : Fin n → ℝ) (j : Fin n),
      HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0) :
    ContDiff ℝ (m + 1) f ∧
      (∀ t, HasFDerivAt f (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) t) ∧
      ∀ k, k ≤ m → ∀ t, ‖iteratedFDeriv ℝ (k + 1) f t‖ ≤ ∑ j, ‖iteratedFDeriv ℝ k (g j) t‖ := by p2m_exact_reverting @_root_.P2MW.S_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single.solution
