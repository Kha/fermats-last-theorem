module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet

@[expose] public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet q k) (h1728 : a ≠ 1728) :
    (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))).eval (a - 1728)⁻¹ = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet.solution
