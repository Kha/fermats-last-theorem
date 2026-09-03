import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_eq_integralClosure_of_etale_of_span_eq_top

universe u

theorem Subalgebra.eq_integralClosure_of_etale_of_span_eq_top
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type u} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A) [Module.Finite R ↥S] [Algebra.Etale R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) :
    S = integralClosure R A := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_eq_integralClosure_of_etale_of_span_eq_top.solution
