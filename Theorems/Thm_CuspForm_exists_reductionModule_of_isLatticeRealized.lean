import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_PowerSeries_FormalHeckeOperators
import P2M.Util
import P2M.Sol.S_CuspForm_exists_reductionModule_of_isLatticeRealized

theorem CuspForm.exists_reductionModule_of_isLatticeRealized {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) {a : ℕ → ℤ} (h1 : a 1 = 1) (hreal : CuspForm.IsLatticeRealized N a) : ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) M) (red : PowerSeries ℤ → M), (∀ g, (∀ n, (3 : ℤ) ∣ PowerSeries.coeff n g) → red g = 0) ∧ (∀ g, red g = 0 → (3 : ℤ) ∣ PowerSeries.coeff 1 g) ∧ (3 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) • red (bridgeProduct a) = 0 ∧ ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), (CuspForm.heckeAlgebra.T hℓ hℓN hℓN - ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})) • red (bridgeProduct a) = red (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_reductionModule_of_isLatticeRealized.solution
