import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import P2M.Util
import P2M.Sol.S_ModularCurve_NodeLocalized_finite_residueField_coeffSubring
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.finite_residueField_coeffSubring
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hq : ((q : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    [IsLocalRing ↥(coeffSubring A K)] :
    Finite (IsLocalRing.ResidueField ↥(coeffSubring A K)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_finite_residueField_coeffSubring.solution
