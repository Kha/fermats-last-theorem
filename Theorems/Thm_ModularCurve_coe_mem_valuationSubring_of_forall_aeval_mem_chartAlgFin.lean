import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    (W₀ : ValuationSubring ↥K)
    (hAW₀ : ∀ a : A, algebraMap A ↥K a ∈ W₀)
    (hjW₀ : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 → Polynomial.aeval j P ∈ W₀) :
    ∀ s : ↥(chartAlgFin A (↥K) j), (s : ↥K) ∈ W₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin.solution
