import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_integralClosure_le_of_isUnit_discr_of_span_eq_top

set_option autoImplicit false

theorem Algebra.integralClosure_le_of_isUnit_discr_of_span_eq_top
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [FiniteDimensional K A]
    (S : Subalgebra R A) (hS : Submodule.span K ((S : Subalgebra R A) : Set A) = ⊤)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) (hdisc : IsUnit (Algebra.discr R b)) :
    integralClosure R A ≤ S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_integralClosure_le_of_isUnit_discr_of_span_eq_top.solution
