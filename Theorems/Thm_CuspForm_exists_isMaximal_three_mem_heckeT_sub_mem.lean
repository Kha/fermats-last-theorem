import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_PowerSeries_FormalHeckeOperators
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isMaximal_three_mem_heckeT_sub_mem

theorem CuspForm.exists_isMaximal_three_mem_heckeT_sub_mem {N : ℕ} [NeZero N] {a : ℕ → ℤ} (h1 : a 1 = 1) (hT : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a)) {M : Type*} [AddCommGroup M] [Module (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) M] (red : PowerSeries ℤ → M) (hker : ∀ g : PowerSeries ℤ, (∀ n, (3 : ℤ) ∣ PowerSeries.coeff n g) → red g = 0) (hker' : ∀ g : PowerSeries ℤ, red g = 0 → (3 : ℤ) ∣ PowerSeries.coeff 1 g) (h3M : (3 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) • red (bridgeProduct a) = 0) (hop : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), (CuspForm.heckeAlgebra.T hℓ hℓN hℓN - ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})) • red (bridgeProduct a) = red (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a)) : ∃ 𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}), 𝔪₁.IsMaximal ∧ ((3 : ℕ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ ∧ ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), CuspForm.heckeAlgebra.T hℓ hℓN hℓN - ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isMaximal_three_mem_heckeT_sub_mem.solution
