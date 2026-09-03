import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Data.Int.ModEq
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isSemistableModel_of_modEq

theorem WeierstrassCurve.isSemistableModel_of_modEq {W W' : WeierstrassCurve ℤ} {n : ℤ} (hW : W.IsSemistableModel) (h₁ : W'.a₁ ≡ W.a₁ [ZMOD n]) (h₂ : W'.a₂ ≡ W.a₂ [ZMOD n]) (h₃ : W'.a₃ ≡ W.a₃ [ZMOD n]) (h₄ : W'.a₄ ≡ W.a₄ [ZMOD n]) (h₆ : W'.a₆ ≡ W.a₆ [ZMOD n]) (haway : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ n → (p : ℤ) ∣ W'.c₄ → ¬ (p : ℤ) ∣ W'.c₆) : W'.IsSemistableModel := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isSemistableModel_of_modEq.solution
