import Mathlib
import P2M.Util
import P2M.Sol.S_HopfOrder_finrank_eq_finrank

open scoped TensorProduct
theorem HopfOrder.finrank_eq_finrank
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤) :
    Module.finrank R ↥S = Module.finrank K A := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_finrank_eq_finrank.solution
