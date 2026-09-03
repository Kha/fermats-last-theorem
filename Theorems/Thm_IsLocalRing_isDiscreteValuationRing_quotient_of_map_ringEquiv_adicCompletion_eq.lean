import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isDiscreteValuationRing_quotient_of_map_ringEquiv_adicCompletion_eq
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.isDiscreteValuationRing_quotient_of_map_ringEquiv_adicCompletion_eq
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (S : Type) [CommRing S] (e : AdicCompletion (maximalIdeal R) R ≃+* S)
    (Q : Ideal R) [Q.IsPrime] (P : Ideal S) [P.IsPrime]
    (hP : Q.map ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) = P)
    [IsDiscreteValuationRing (S ⧸ P)] :
    IsDiscreteValuationRing (R ⧸ Q) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isDiscreteValuationRing_quotient_of_map_ringEquiv_adicCompletion_eq.solution
