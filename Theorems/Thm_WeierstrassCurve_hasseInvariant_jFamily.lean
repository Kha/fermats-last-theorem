module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_hasseInvariant_jFamily

@[expose] public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.hasseInvariant_jFamily
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (m e₄ e₆ : ℕ) (hm : 12 * m + 4 * e₄ + 6 * e₆ = q - 1) (he₄ : e₄ ≤ 2) (he₆ : e₆ ≤ 1)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k)) =
      (1 + 1728 * Polynomial.X) ^ (2 * m + e₄ + e₆) *
        ∏ a ∈ S₀ \ {0, 1728}, (1 + Polynomial.C (1728 - a) * Polynomial.X) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_hasseInvariant_jFamily.solution
