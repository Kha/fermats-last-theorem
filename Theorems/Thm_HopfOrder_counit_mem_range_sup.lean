import Mathlib
import P2M.Util
import P2M.Sol.S_HopfOrder_counit_mem_range_sup

universe u v w
theorem HopfOrder.counit_mem_range_sup
    {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] {S S' : Subalgebra R A}
    (hS : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hS' : ∀ x ∈ S', Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    ∀ x ∈ S ⊔ S', Coalgebra.counit (R := K) x ∈ (algebraMap R K).range := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_counit_mem_range_sup.solution
