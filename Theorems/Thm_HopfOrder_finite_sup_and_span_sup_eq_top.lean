import Mathlib
import P2M.Util
import P2M.Sol.S_HopfOrder_finite_sup_and_span_sup_eq_top

universe u v w
theorem HopfOrder.finite_sup_and_span_sup_eq_top
    {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] {S S' : Subalgebra R A}
    [Module.Finite R S] [Module.Finite R S'] (hspan : Submodule.span K (S : Set A) = ⊤) :
    Module.Finite R ↥(S ⊔ S') ∧ Submodule.span K ((S ⊔ S' : Subalgebra R A) : Set A) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_finite_sup_and_span_sup_eq_top.solution
