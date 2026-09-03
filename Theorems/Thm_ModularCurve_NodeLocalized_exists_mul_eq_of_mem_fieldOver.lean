import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import P2M.Util
import P2M.Sol.S_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.exists_mul_eq_of_mem_fieldOver
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ fieldOver (1 * q) K) :
    ∃ y z : LaurentSeries (AlgebraicClosure ℚ),
      y ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ∧
      z ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ∧
      z ≠ 0 ∧ x * z = y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver.solution
