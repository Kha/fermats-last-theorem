import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isPrime_map_adicCompletion_and_eq_of_le_of_isDiscreteValuationRing_quotient
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.isPrime_map_adicCompletion_and_eq_of_le_of_isDiscreteValuationRing_quotient
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (Q : Ideal R) [Q.IsPrime] [IsDomain (R ⧸ Q)] [IsDiscreteValuationRing (R ⧸ Q)] :
    (Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).IsPrime ∧
    ∀ P : Ideal (AdicCompletion (maximalIdeal R) R), P.IsPrime →
      Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≤ P → ¬ P.IsMaximal →
      P = Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isPrime_map_adicCompletion_and_eq_of_le_of_isDiscreteValuationRing_quotient.solution
