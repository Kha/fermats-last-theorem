import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Definitions.Def_ModularCurve_NodeDescent
import P2M.Util
import P2M.Sol.S_ModularCurve_LambdaNodeLocalized_exists_mul_eq_of_mem_lambdaFieldOver
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized

theorem ModularCurve.LambdaNodeLocalized.exists_mul_eq_of_mem_lambdaFieldOver
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (l : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ lambdaFieldOver q K) :
    ∃ y z : LaurentSeries (AlgebraicClosure ℚ),
      y ∈ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) ∧
      z ∈ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) ∧
      z ≠ 0 ∧ x * z = y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_mul_eq_of_mem_lambdaFieldOver.solution
