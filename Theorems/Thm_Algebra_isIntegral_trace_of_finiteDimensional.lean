import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isIntegral_trace_of_finiteDimensional

set_option autoImplicit false

theorem Algebra.isIntegral_trace_of_finiteDimensional
    {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    {A : Type*} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [FiniteDimensional K A]
    {x : A} (hx : IsIntegral R x) :
    IsIntegral R (Algebra.trace K A x) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isIntegral_trace_of_finiteDimensional.solution
