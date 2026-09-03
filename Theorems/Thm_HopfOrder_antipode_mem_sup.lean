import Mathlib
import P2M.Util
import P2M.Sol.S_HopfOrder_antipode_mem_sup

universe u v w
theorem HopfOrder.antipode_mem_sup
    {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] {S S' : Subalgebra R A}
    (hS : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) (hS' : ∀ x ∈ S', HopfAlgebra.antipode K x ∈ S') :
    ∀ x ∈ S ⊔ S', HopfAlgebra.antipode K x ∈ S ⊔ S' := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_antipode_mem_sup.solution
