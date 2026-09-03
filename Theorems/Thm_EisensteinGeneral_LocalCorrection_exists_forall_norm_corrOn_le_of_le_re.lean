import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_EisensteinGeneral_LocalCorrection
import P2M.Util
import P2M.Sol.S_EisensteinGeneral_LocalCorrection_exists_forall_norm_corrOn_le_of_le_re

set_option autoImplicit false

open EisensteinGeneral.LocalCorrection

theorem EisensteinGeneral.LocalCorrection.exists_forall_norm_corrOn_le_of_le_re
    {N : ℕ} (hN : 2 ≤ N) (n : ℤ) (c₀ m₀ : ℕ) {μ𝒪 : ℝ} (hμ : 0 < μ𝒪)
    (c₀' b d σ₁ : ℝ) (hc₀' : 0 ≤ c₀') (hb : 0 ≤ b) (hd : 1 ≤ d) :
    ∃ E : ℝ, ∃ κ : ℕ, 0 ≤ E ∧ ∀ (c m : ℕ) (e : ℤ) (γ₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ),
      c ≤ c₀ → m ≤ m₀ → ‖γ₀‖ ≤ c₀' → (∀ k, 1 ≤ k → ‖sh k‖ ≤ b * d ^ k) → σ₁ ≤ s.re →
        ‖corrOn N n c m e μ𝒪 γ₀ sh s‖ ≤ E * ((N : ℝ) ^ (-e).toNat) ^ κ := by p2m_exact_reverting @_root_.P2MW.S_EisensteinGeneral_LocalCorrection_exists_forall_norm_corrOn_le_of_le_re.solution
