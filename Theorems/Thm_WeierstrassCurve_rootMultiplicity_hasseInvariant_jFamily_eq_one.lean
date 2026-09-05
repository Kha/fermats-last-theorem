module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_rootMultiplicity_hasseInvariant_jFamily_eq_one

@[expose] public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.rootMultiplicity_hasseInvariant_jFamily_eq_one
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet q k) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    Polynomial.rootMultiplicity (a - 1728)⁻¹ (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))) = 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_rootMultiplicity_hasseInvariant_jFamily_eq_one.solution
