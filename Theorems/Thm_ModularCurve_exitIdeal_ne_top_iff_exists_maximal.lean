import Mathlib
import Definitions.Def_ModularCurve_SupportTransfer
import P2M.Util
import P2M.Sol.S_ModularCurve_exitIdeal_ne_top_iff_exists_maximal

theorem ModularCurve.exitIdeal_ne_top_iff_exists_maximal (N : ℕ) [NeZero N] (W : WeierstrassCurve ℤ) (p : ℕ) :
    ModularCurve.exitIdeal N W p ≠ ⊤ ↔
      ∃ 𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}), 𝔪₁.IsMaximal ∧
        ((p : ℕ) : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) ∈ 𝔪₁ ∧
        ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), W.IsGoodPrimeFor ℓ → ℓ ≠ p →
          ModularCurve.exitGen N W ℓ hℓ hℓN ∈ 𝔪₁ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exitIdeal_ne_top_iff_exists_maximal.solution
