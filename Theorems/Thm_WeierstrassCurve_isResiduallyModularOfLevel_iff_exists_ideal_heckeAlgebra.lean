import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isResiduallyModularOfLevel_iff_exists_ideal_heckeAlgebra

theorem WeierstrassCurve.isResiduallyModularOfLevel_iff_exists_ideal_heckeAlgebra (W : WeierstrassCurve ℤ) {p M : ℕ} [NeZero M] (hM : CuspForm.HasIntegralStructure M 2) : W.IsResiduallyModularOfLevel p M ↔ ∃ 𝔪 : Ideal (CuspForm.heckeAlgebra M 2 {ℓ | ¬ W.IsGoodPrimeFor ℓ ∨ ℓ = p ∨ ℓ ∣ M}), 𝔪.IsMaximal ∧ (p : CuspForm.heckeAlgebra M 2 {ℓ | ¬ W.IsGoodPrimeFor ℓ ∨ ℓ = p ∨ ℓ ∣ M}) ∈ 𝔪 ∧ ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ {ℓ | ¬ W.IsGoodPrimeFor ℓ ∨ ℓ = p ∨ ℓ ∣ M}), CuspForm.heckeAlgebra.T hℓ hℓM hℓS - (W.apOfModel ℓ : CuspForm.heckeAlgebra M 2 {ℓ | ¬ W.IsGoodPrimeFor ℓ ∨ ℓ = p ∨ ℓ ∣ M}) ∈ 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_iff_exists_ideal_heckeAlgebra.solution
