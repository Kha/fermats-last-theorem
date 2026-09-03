import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_QuasiFinite_of_flat_of_quasiFinite_genericFiber

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.QuasiFinite.of_flat_of_quasiFinite_genericFiber
    {R B K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.DimensionLEOne R]
    [CommRing B] [Algebra R B] [Module.Flat R B] [Algebra.FiniteType R B]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hgen : Algebra.QuasiFinite K (K ⊗[R] B)) : Algebra.QuasiFinite R B := by p2m_exact_reverting @_root_.P2MW.S_Algebra_QuasiFinite_of_flat_of_quasiFinite_genericFiber.solution
