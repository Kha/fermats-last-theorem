import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ValuationSubring.toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian
    {K F : Type} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] [HenselianLocalRing O]
    [Algebra O F] [IsScalarTower O K F]
    (O' : ValuationSubring F) (hO' : ∀ x : K, algebraMap K F x ∈ O' ↔ x ∈ O) :
    O'.toSubring = (integralClosure O F).toSubring ∧ Module.Finite O (integralClosure O F) ∧
      IsDiscreteValuationRing (integralClosure O F) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian.solution
