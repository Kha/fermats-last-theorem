import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Data.Int.ModEq
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_isIntegralModelOf_of_dvd

theorem WeierstrassCurve.exists_isIntegralModelOf_of_dvd (W : WeierstrassCurve ℤ) (A B n : ℤ) (hA : 46656 * n ∣ A + 27 * W.c₄) (hB : 93312 * n ∣ B + 54 * W.c₆) : ∃ W' : WeierstrassCurve ℤ, W'.IsIntegralModelOf ⟨0, 0, 0, A, B⟩ ∧ W'.a₁ = W.a₁ ∧ W'.a₂ = W.a₂ ∧ W'.a₃ = W.a₃ ∧ W'.a₄ ≡ W.a₄ [ZMOD n] ∧ W'.a₆ ≡ W.a₆ [ZMOD n] ∧ -27 * W'.c₄ = A ∧ -54 * W'.c₆ = B := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_isIntegralModelOf_of_dvd.solution
