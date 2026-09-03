import Mathlib
import P2M.Util
import P2M.Sol.S_HopfOrder_integralClosure_finite_of_etale

universe u v w
theorem HopfOrder.integralClosure_finite_of_etale
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type w} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [Algebra.Etale K A] : Module.Finite R ↥(integralClosure R A) := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_integralClosure_finite_of_etale.solution
