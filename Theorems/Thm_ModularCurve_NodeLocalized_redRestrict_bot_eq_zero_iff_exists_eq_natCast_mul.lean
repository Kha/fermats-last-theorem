import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import P2M.Util
import P2M.Sol.S_ModularCurve_NodeLocalized_redRestrict_bot_eq_zero_iff_exists_eq_natCast_mul
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.redRestrict_bot_eq_zero_iff_exists_eq_natCast_mul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (c : ↥(coeffSubring A ⊥)) :
    redRestrict red ⊥ c = 0 ↔ ∃ d, c = ((q : ℕ) : ↥(coeffSubring A ⊥)) * d := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_redRestrict_bot_eq_zero_iff_exists_eq_natCast_mul.solution
