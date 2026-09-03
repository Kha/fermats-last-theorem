import Mathlib
import P2M.Util
import P2M.Sol.S_integralClosure_moduleFinite_of_isReduced_of_charZero

set_option autoImplicit false

theorem integralClosure.moduleFinite_of_isReduced_of_charZero
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [CommRing L] [IsReduced L] [Algebra K L] [Module.Finite K L]
    [Algebra R L] [IsScalarTower R K L] :
    Module.Finite R (integralClosure R L) := by p2m_exact_reverting @_root_.P2MW.S_integralClosure_moduleFinite_of_isReduced_of_charZero.solution
