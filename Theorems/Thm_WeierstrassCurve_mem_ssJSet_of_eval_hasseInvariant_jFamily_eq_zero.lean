module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero

@[expose] public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (t₀ : k) (h : (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))).eval t₀ = 0)
    (hc : 1 + 1728 * t₀ ≠ 0) :
    t₀ ≠ 0 ∧ 1728 + t₀⁻¹ ∈ ssJSet q k := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero.solution
