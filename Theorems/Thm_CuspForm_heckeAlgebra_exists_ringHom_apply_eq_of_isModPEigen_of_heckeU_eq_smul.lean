import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_PowerSeries_FormalHeckeOperators
import P2M.Util
import P2M.Sol.S_CuspForm_heckeAlgebra_exists_ringHom_apply_eq_of_isModPEigen_of_heckeU_eq_smul
set_option autoImplicit false
open CuspForm ModPForms

theorem CuspForm.heckeAlgebra.exists_ringHom_apply_eq_of_isModPEigen_of_heckeU_eq_smul
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ) (k : ℤ) (hk : 2 ≤ k)
    (F : Type) [Field F] [CharP F p]
    (φ : PowerSeries F) (lam mu : ℕ → F) (hφ : φ ∈ modPCusp N k F) (heig : IsModPEigen N S k φ lam)
    (heigU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S), PowerSeries.heckeU q φ = mu q • φ) :
    ∃ θ : heckeAlgebra N k S →+* F,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), θ (heckeAlgebra.T hℓ hℓN hℓS) = lam ℓ) ∧
      ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S), θ (heckeAlgebra.U hq hqN hqS) = mu q := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_apply_eq_of_isModPEigen_of_heckeU_eq_smul.solution
