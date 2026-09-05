module

public import Mathlib
public import Definitions.Def_ModularCurve_NodeDescent
import P2M.Util
import P2M.Sol.S_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing

@[expose] public section
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized
theorem ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing
    (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] :
    coeffSubring A K = K.toSubalgebra.toSubring ∨ IsDiscreteValuationRing ↥(coeffSubring A K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing.solution
