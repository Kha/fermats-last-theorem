import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_QuasiFinite_of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Algebra.QuasiFinite.of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type w) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [Module.Flat R S]
    [Module.Finite K (K ⊗[R] S)] :
    Algebra.QuasiFinite R S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_QuasiFinite_of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing.solution
